"""Read-only, immutable-input replay with a Python audit guard (not an OS sandbox)."""
import argparse
from fractions import Fraction
from functools import lru_cache
import hashlib
from itertools import combinations
import json
from math import gcd
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
from types import MappingProxyType

EXP = Path(__file__).resolve().parent
ROOT = EXP.parents[2]
PREFIX = "frontier/experiments/i175_affected_prism_exterior/"
SPREFIX = "frontier/sources/i175_affected_prism_exterior/"
REPORT = "frontier/iterations/i175-affected-prism-exterior.md"
CONTROLS = [PREFIX+x for x in ("inventory.json", "prevalidation.json", "seal.json")]
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def encode(x):
    return (json.dumps(x, sort_keys=True, indent=2)+"\n").encode()


def owned_names():
    names = {REPORT}
    for prefix in (PREFIX, SPREFIX):
        for p in (ROOT / prefix).rglob("*"):
            assert not p.is_symlink(), str(p)
            if p.is_file():
                names.add(str(p.relative_to(ROOT)))
    return names-set(CONTROLS)


def verify(prevalidation=False):
    start = time.perf_counter()
    control_bytes = {CONTROLS[0]: (ROOT / CONTROLS[0]).read_bytes()}
    inv = json.loads(control_bytes[CONTROLS[0]])
    assert inv["iteration"] == 175
    assert inv["controls"] == CONTROLS
    assert [x["path"] for x in inv["context"]] == CONTEXT
    assert owned_names() == {x["path"] for x in inv["owned"]}
    assert len({x["path"] for x in inv["owned"]+inv["external"]}) == len(inv["owned"])+len(inv["external"])
    assert not set(CONTEXT) & {x["path"] for x in inv["owned"]+inv["external"]}
    memory = {}
    for item in inv["owned"]+inv["external"]:
        p = ROOT / item["path"]
        assert not p.is_symlink()
        b = p.read_bytes()
        assert len(b) == item["size"] and sha(b) == item["sha256"], item["path"]
        memory[item["path"]] = b
    current_context = {p: (ROOT / p).read_bytes() for p in CONTEXT}
    for item in inv["context"]:
        assert sha(current_context[item["path"]]) == item["sha256"], "context changed during I175 preparation"
    if not prevalidation:
        for name in CONTROLS[1:]:
            control_bytes[name] = (ROOT / name).read_bytes()
        seal = json.loads(control_bytes[CONTROLS[2]])
        assert seal["inventory_sha256"] == sha(control_bytes[CONTROLS[0]])
        assert seal["prevalidation_sha256"] == sha(control_bytes[CONTROLS[1]])
        assert seal["report_sha256"] == sha(memory[REPORT])
        assert seal["verifier_sha256"] == sha(memory[PREFIX+"verify175.py"])
        assert json.loads(control_bytes[CONTROLS[1]])["status"] == "PASS"

    allowed_sources = {str(ROOT / (PREFIX+name)): memory[PREFIX+name]
                       for name in ("math175.py", "research175.py")}
    allowed_codes = set()
    outsider = compile("pass", "<precompiled-unowned-probe>", "exec")
    guard = {"active": False}

    def audit(event, args):
        if not guard["active"]:
            return
        if event == "open":
            raise PermissionError("filesystem access blocked")
        if event.startswith(("socket.", "subprocess.", "os.exec", "os.spawn")):
            raise PermissionError("network/process blocked")
        if event in ("os.mkdir", "os.rmdir", "os.remove", "os.rename", "os.link", "os.symlink",
                     "os.chmod", "os.chown", "os.truncate", "os.utime", "os.chdir",
                     "os.system", "os.fork", "os.listdir", "os.scandir", "os.putenv",
                     "os.unsetenv", "shutil.copyfile"):
            raise PermissionError("mutation or unbound filesystem query blocked")
        if event == "compile":
            source, name = args
            if isinstance(source, str):
                source = source.encode()
            if name not in allowed_sources or source != allowed_sources[name]:
                raise PermissionError("unowned or forged compilation blocked")
        if event == "exec" and args[0] not in allowed_codes:
            raise PermissionError("unowned execution blocked")

    sys.addaudithook(audit)
    guard["active"] = True
    results = []
    try:
        probes = [
            ("write", lambda: open(str(EXP / "forbidden-probe.tmp"), "w")),
            ("mutation", lambda: os.mkdir(str(EXP / "forbidden-probe-dir"))),
            ("network", lambda: socket.socket()),
            ("subprocess", lambda: subprocess.Popen([sys.executable, "-c", "pass"])),
            ("unbound-read", lambda: open(str(ROOT / "unbound-probe.txt"), "rb")),
            ("outside-compile", lambda: compile("pass", "<outside-probe>", "exec")),
            ("outside-exec", lambda: exec(outsider, {})),
            ("forged-owned-source", lambda: compile(b"pass", str(EXP / "math175.py"), "exec")),
        ]
        for label, action in probes:
            try:
                action()
            except PermissionError:
                results.append({"probe": label, "blocked": True})
            else:
                raise AssertionError(("guard probe escaped", label))
        namespace = {"INPUT": MappingProxyType(memory)}
        for filename, source in allowed_sources.items():
            code = compile(source, filename, "exec")
            allowed_codes.add(code)
            exec(code, namespace)
        comparisons = []
        for task in inv["replays"]:
            when = time.perf_counter()
            payload = encode(namespace[task["function"]]())
            assert payload == memory[task["payload"]], task["function"]
            comparisons.append({"function": task["function"], "payload": task["payload"],
                                "byte_identical": True, "sha256": sha(payload),
                                "seconds": time.perf_counter()-when})
    finally:
        guard["active"] = False
    # Nothing may have changed, including the current context bytes and controls.
    for path, b in memory.items():
        assert (ROOT / path).read_bytes() == b, ("changed", path)
    for path, b in {**control_bytes, **current_context}.items():
        assert (ROOT / path).read_bytes() == b, ("changed control/context", path)
    assert owned_names() == {x["path"] for x in inv["owned"]}
    return {"iteration": 175, "status": "PASS", "prevalidation": prevalidation,
            "owned": len(inv["owned"]), "external": len(inv["external"]),
            "context": len(inv["context"]), "external_context_total": len(inv["external"])+4,
            "inventory_sha256": sha(control_bytes[CONTROLS[0]]),
            "report_sha256": sha(memory[REPORT]),
            "verifier_sha256": sha(memory[PREFIX+"verify175.py"]),
            "seal_sha256": None if prevalidation else sha(control_bytes[CONTROLS[2]]),
            "comparisons": comparisons, "probes": results,
            "before_after": "all bound bytes, complete owned file set, controls and current contexts unchanged",
            "runtime_seconds": time.perf_counter()-start,
            "limits": "Python audit guard, not OS sandboxing; clean-clone reconstruction not tested"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--prevalidate", action="store_true")
    args = parser.parse_args()
    sys.stdout.buffer.write(encode(verify(args.prevalidate)))
