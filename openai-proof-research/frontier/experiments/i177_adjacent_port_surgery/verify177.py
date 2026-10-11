"""Immutable-first, read-only mathematical replay with eight explicit audit probes.

This is a Python audit guard, not an operating-system security boundary.
"""
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import types
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import gcd, lcm

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
BASE = ROOT / "frontier/experiments/i177_adjacent_port_surgery"
SOURCE = ROOT / "frontier/sources/i177_adjacent_port_surgery"
REPORT = ROOT / "frontier/iterations/i177-adjacent-port-surgery.md"
CONTEXTS = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
            "frontier/iterations/README.md"}
CONTROL_NAMES = ("inventory.json", "prevalidation.json", "seal.json")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def membership():
    return {str(REPORT.relative_to(ROOT))} | {
        str(p.relative_to(ROOT)) for directory in (BASE, SOURCE)
        for p in directory.rglob("*") if p.is_file()}


def main():
    start = time.perf_counter()
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert prevalidate or not sys.argv[1:]
    invpath = BASE / "inventory.json"
    rawinv = invpath.read_bytes()
    inv = json.loads(rawinv)
    assert {e["path"] for e in inv["context"]} == CONTEXTS
    owned = {e["path"] for e in inv["owned"]}
    external = {e["path"] for e in inv["external"]}
    assert len(owned) == len(inv["owned"]) and len(external) == len(inv["external"])
    assert not (owned & external) and not ((owned | external) & CONTEXTS)
    controls = {str((BASE / n).relative_to(ROOT)) for n in CONTROL_NAMES}
    assert set(inv["controls"]) == controls
    expected_controls = {str(invpath.relative_to(ROOT))} if prevalidate else controls
    assert membership() == owned | expected_controls
    # Load and authenticate every mathematical input before any owned code runs.
    frozen = {}
    before = {}
    for e in inv["owned"] + inv["external"]:
        path = ROOT / e["path"]
        data = path.read_bytes()
        assert (len(data), sha(data)) == (e["size"], e["sha256"]), e["path"]
        frozen[str(path)] = data
        before[e["path"]] = sha(data)
    for rel in expected_controls:
        data = (ROOT / rel).read_bytes()
        frozen[str(ROOT / rel)] = data
        before[rel] = sha(data)
    contexts_before = {rel: sha((ROOT / rel).read_bytes()) for rel in sorted(CONTEXTS)}
    sealed = None
    if not prevalidate:
        sealed = json.loads(frozen[str(BASE / "seal.json")])
        pre = json.loads(frozen[str(BASE / "prevalidation.json")])
        assert sealed["inventory_sha256"] == sha(rawinv)
        assert sealed["prevalidation_sha256"] == sha(frozen[str(BASE / "prevalidation.json")])
        assert sealed["report_sha256"] == sha(frozen[str(REPORT)])
        assert sealed["verifier_sha256"] == sha(frozen[str(BASE / "verify177.py")])
        assert pre["status"] == "PASS" and pre["prevalidation"] is True
        assert pre["inventory_sha256"] == sha(rawinv)
        assert pre["report_sha256"] == sealed["report_sha256"]
        assert pre["verifier_sha256"] == sealed["verifier_sha256"]
        assert len(pre["probes"]) == 8 and all(r["blocked"] for r in pre["probes"])
        assert len(pre["comparisons"]) == 3 and all(r["byte_identical"] for r in pre["comparisons"])
        assert pre["context_before"] == pre["context_after"]
    readonly = types.MappingProxyType(frozen)
    executable = {str(BASE / name): frozen[str(BASE / name)] for name in ("math177.py", "research177.py")}
    # Only these exact owned code-object trees may subsequently be executed.
    allowed_codes = set()
    def register(code):
        allowed_codes.add(code)
        for c in code.co_consts:
            if isinstance(c, types.CodeType):
                register(c)
    codes = {}
    for path, data in executable.items():
        code = compile(data, path, "exec")
        register(code)
        codes[path] = code
    outside_code = compile("pass", "<I177-outside-probe>", "exec")
    allowed_reads = set(frozen) | {str(ROOT / rel) for rel in CONTEXTS}

    def guard(event, args):
        if event == "open":
            name, mode, flags = args
            if (isinstance(mode, str) and any(c in mode for c in "wax+")) or (
                    flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
                raise PermissionError("I177 write blocked")
            if not isinstance(name, (str, bytes, os.PathLike)):
                raise PermissionError("I177 descriptor read blocked")
            path = os.fsdecode(name)
            if os.path.abspath(path) not in allowed_reads:
                raise PermissionError("I177 unbound read blocked")
        if event in {"os.remove", "os.rename", "os.mkdir", "os.rmdir", "os.chmod",
                     "os.chown", "os.link", "os.symlink", "os.truncate", "os.utime",
                     "os.chdir", "os.putenv", "os.unsetenv"}:
            raise PermissionError("I177 mutation blocked")
        if event.startswith("socket."):
            raise PermissionError("I177 network blocked")
        if event.startswith("subprocess.") or event in {"os.system", "os.exec", "os.fork", "os.posix_spawn"}:
            raise PermissionError("I177 process blocked")
        if event == "compile":
            source, filename = args
            source = source.encode() if isinstance(source, str) else source
            if filename not in executable or source != executable[filename]:
                raise PermissionError("I177 unbound or forged compilation blocked")
        if event == "exec" and args[0] not in allowed_codes:
            raise PermissionError("I177 outside execution blocked")
    sys.addaudithook(guard)
    operations = [
        ("write", lambda: open(BASE / "blocked-write-probe", "wb")),
        ("mutation", lambda: os.mkdir(BASE / "blocked-mkdir-probe")),
        ("network", lambda: socket.socket()),
        ("subprocess", lambda: subprocess.run([sys.executable, "--version"], capture_output=True)),
        ("unbound-read", lambda: open(ROOT / "i177-unbound-probe", "rb")),
        ("outside-compile", lambda: compile("pass", "<I177-unbound>", "exec")),
        ("outside-exec", lambda: exec(outside_code, {})),
        ("forged-owned-source", lambda: compile(executable[str(BASE / "math177.py")]+b"\n# forged\n",
                                                str(BASE / "math177.py"), "exec")),
    ]
    probes = []
    for name, action in operations:
        try:
            action()
        except PermissionError:
            probes.append({"probe": name, "blocked": True})
        else:
            raise AssertionError(("probe unexpectedly allowed", name))
    namespace = {"__name__": "i177_replay", "INPUT_BYTES": readonly}
    stdout, stderr = io.StringIO(), io.StringIO()
    comparisons = []
    with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
        for path in executable:
            exec(codes[path], namespace)
        for case in inv["replays"]:
            then = time.perf_counter()
            obj = namespace[case["function"]]()
            payload = (json.dumps(obj, indent=2, sort_keys=True)+"\n").encode()
            assert payload == frozen[str(ROOT / case["payload"])], case["function"]
            comparisons.append({"function": case["function"], "byte_identical": True,
                                "sha256": sha(payload), "seconds": time.perf_counter()-then})
    assert stdout.getvalue() == stderr.getvalue() == ""
    after = {rel: sha((ROOT / rel).read_bytes()) for rel in before}
    contexts_after = {rel: sha((ROOT / rel).read_bytes()) for rel in contexts_before}
    assert before == after
    assert contexts_before == contexts_after
    assert membership() == owned | expected_controls
    result = {
        "status": "PASS", "iteration": 177, "prevalidation": prevalidate,
        "owned": len(owned), "external": len(external), "contexts": 4,
        "inventory_sha256": sha(rawinv), "report_sha256": sha(frozen[str(REPORT)]),
        "verifier_sha256": sha(frozen[str(BASE / "verify177.py")]),
        "seal_sha256": None if prevalidate else sha(frozen[str(BASE / "seal.json")]),
        "comparisons": comparisons, "probes": probes, "stderr_empty": True,
        "context_before": contexts_before, "context_after": contexts_after,
        "context_history": inv["context"],
        "before_after": "Strict mathematics, controls, complete membership, and current context bytes unchanged",
        "limits": "Python audit guard, not OS sandbox; no clean-clone test; no ancestor execution",
        "runtime_seconds": time.perf_counter()-start,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
