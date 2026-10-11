"""Read-only authenticated I180 replay. Python audit guard, not an OS sandbox."""
import fractions
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import types

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
PREFIX = "frontier/experiments/i180_survivor_helper_connectivity/"
HERE = ROOT / PREFIX
REPORT = "frontier/iterations/i180-survivor-helper-connectivity.md"
CONTEXT = ["README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"]
CONTROLS = [PREFIX + p for p in ("inventory.json", "prevalidation.json", "seal.json")]
MODULES = ["math180", "research180"]


def digest(b):
    return hashlib.sha256(b).hexdigest()


def encoded(x):
    return (json.dumps(x, sort_keys=True, indent=2) + "\n").encode()


def read(p):
    f = ROOT / p
    assert f.is_file() and not f.is_symlink(), p
    return f.read_bytes()


def listing(stem, report):
    out = {report}
    for part in ("experiments", "sources"):
        root = ROOT / ("frontier/" + part + "/" + stem)
        assert root.is_dir()
        for f in root.rglob("*"):
            assert not f.is_symlink(), str(f)
            if f.is_file():
                out.add(str(f.relative_to(ROOT)))
    return out


def current_membership():
    return {
        "owned": sorted(listing("i180_survivor_helper_connectivity", REPORT)),
        "I179": sorted(listing("i179_path_recombination", "frontier/iterations/i179-path-recombination.md")),
        "I178": sorted(listing("i178_five_port_annihilator", "frontier/iterations/i178-five-port-annihilator.md")),
        "parent": sorted(str(f.relative_to(ROOT)) for f in (ROOT / "frontier/experiments").glob("i179-parent-*")
                         if f.is_file()),
    }


def verify(prevalidate=False):
    start = time.monotonic()
    inv_bytes = read(CONTROLS[0])
    inv = json.loads(inv_bytes)
    assert inv["iteration"] == 180 and inv["controls"] == CONTROLS
    assert sorted(e["path"] for e in inv["context"]) == sorted(CONTEXT)
    data = {}
    for section in ("owned", "external"):
        assert len({e["path"] for e in inv[section]}) == len(inv[section])
        for entry in inv[section]:
            b = read(entry["path"])
            assert len(b) == entry["size"] and digest(b) == entry["sha256"], entry["path"]
            data[entry["path"]] = b
    assert not set(CONTEXT) & set(data)
    assert not set(CONTROLS) & set(data)
    inputs = json.loads(data[PREFIX + "inputs.json"])
    assert inv["external"] == inputs["strict"] and len(inv["external"]) == 913
    for p, h in inputs["detached_anchors"].items():
        assert digest(data[p]) == h
    ancestor = json.loads(data["frontier/experiments/i179_path_recombination/inventory.json"])
    oldseal = json.loads(data["frontier/experiments/i179_path_recombination/seal.json"])
    oldpre = json.loads(data["frontier/experiments/i179_path_recombination/prevalidation.json"])
    for name in ("inventory", "prevalidation"):
        assert digest(data["frontier/experiments/i179_path_recombination/" + name + ".json"]) == oldseal[name + "_sha256"]
    assert oldpre["status"] == "PASS" and oldpre["prevalidation"]
    original = json.loads(data["frontier/experiments/i179_path_recombination/inputs.json"])
    supplement = json.loads(data["frontier/experiments/i179_path_recombination/supplement.json"])
    assert len(original["strict"]) == 773 and len(supplement["strict"]) == 1
    assert supplement["original_inputs_sha256"] == digest(data["frontier/experiments/i179_path_recombination/inputs.json"])
    assert sorted(original["strict"] + supplement["strict"], key=lambda e: e["path"]) == ancestor["external"]
    for sec in ("owned", "external"):
        for e in ancestor[sec]:
            assert digest(data[e["path"]]) == e["sha256"] and len(data[e["path"]]) == e["size"]
    a178 = json.loads(data["frontier/experiments/i178_five_port_annihilator/inventory.json"])
    s178 = json.loads(data["frontier/experiments/i178_five_port_annihilator/seal.json"])
    for name in ("inventory", "prevalidation"):
        assert digest(data["frontier/experiments/i178_five_port_annihilator/" + name + ".json"]) == s178[name + "_sha256"]
    assert json.loads(data["frontier/experiments/i178_five_port_annihilator/prevalidation.json"])["status"] == "PASS"
    assert json.loads(data["frontier/experiments/i178_five_port_annihilator/inputs.json"])["strict"] == a178["external"]
    before_membership = current_membership()
    assert set(before_membership["owned"]) - set(CONTROLS) == {e["path"] for e in inv["owned"]}
    assert set(before_membership["I179"]) == {e["path"] for e in ancestor["owned"]} | set(ancestor["controls"])
    assert set(before_membership["I178"]) == {e["path"] for e in a178["owned"]} | set(a178["controls"])
    assert set(before_membership["parent"]) == {p for p in data if p.startswith("frontier/experiments/i179-parent-")}
    control_bytes = {p: read(p) if (ROOT / p).exists() else None for p in CONTROLS}
    if prevalidate:
        assert control_bytes[CONTROLS[1]] is None and control_bytes[CONTROLS[2]] is None
    else:
        pre = json.loads(control_bytes[CONTROLS[1]])
        seal = json.loads(control_bytes[CONTROLS[2]])
        assert seal["iteration"] == 180 and pre["status"] == "PASS" and pre["prevalidation"]
        assert seal["inventory_sha256"] == pre["inventory_sha256"] == digest(inv_bytes)
        assert seal["prevalidation_sha256"] == digest(control_bytes[CONTROLS[1]])
        assert seal["report_sha256"] == pre["report_sha256"] == digest(data[REPORT])
        assert seal["verifier_sha256"] == pre["verifier_sha256"] == digest(data[PREFIX + "verify180.py"])
    context_before = {p: read(p) for p in CONTEXT}
    # The only inherited drift exemptions are the four contexts. Their current
    # bytes, not their old inventory hashes, must stay unchanged during this run.
    frozen = types.MappingProxyType(data)
    source = {str(ROOT / (PREFIX + name + ".py")): frozen[PREFIX + name + ".py"] for name in MODULES}
    approved_code = set()
    guard_active = [True]
    mutation_events = {
        "os.remove", "os.rename", "os.rmdir", "os.mkdir", "os.chmod", "os.chown",
        "os.link", "os.symlink", "os.truncate", "os.utime", "os.system",
        "os.fork", "os.forkpty", "os.exec", "os.posix_spawn", "os.putenv",
    }

    class Blocked(RuntimeError):
        pass

    def audit(event, args):
        if not guard_active[0]:
            return
        if event == "open":
            raise Blocked("No filesystem I/O during mathematical replay")
        if event in mutation_events or event.startswith("socket.") or event.startswith("subprocess."):
            raise Blocked("Mutation/network/subprocess denied")
        if event == "compile":
            body, name = args
            if isinstance(body, str):
                body = body.encode()
            if name not in source or not isinstance(body, bytes) or body != source[name]:
                raise Blocked("Only exact frozen owned source may compile")
        if event == "exec" and args[0] not in approved_code:
            raise Blocked("Only registered owned code may execute")
        if event == "import" and args[0] not in sys.modules:
            raise Blocked("No new imports during mathematical replay")

    foreign = compile("pass", "/outside/i180-forbidden.py", "exec")
    sys.addaudithook(audit)
    probes, comparisons = [], []
    try:
        functions = [
            ("write", lambda: open(str(ROOT / REPORT), "ab")),
            ("mutation", lambda: os.unlink(str(ROOT / REPORT))),
            ("network", lambda: socket.socket()),
            ("subprocess", lambda: subprocess.run([sys.executable, "-c", "pass"], check=True)),
            ("unbound-read", lambda: open(str(ROOT / "sources/tree.json"), "rb")),
            ("outside-compile", lambda: compile("pass", "/outside/i180-probe.py", "exec")),
            ("outside-exec", lambda: exec(foreign, {})),
            ("forged-owned-source", lambda: compile("pass", str(ROOT / (PREFIX + "math180.py")), "exec")),
        ]
        for name, operation in functions:
            try:
                operation()
            except Blocked:
                probes.append({"probe": name, "blocked": True})
            else:
                raise AssertionError("Probe was not blocked: " + name)
        for name in MODULES:
            filename = str(ROOT / (PREFIX + name + ".py"))
            code = compile(source[filename], filename, "exec")
            approved_code.add(code)
            module = types.ModuleType(name)
            module.__file__ = filename
            sys.modules[name] = module
            exec(code, module.__dict__)
        research = sys.modules["research180"]
        def load(p):
            assert p in frozen and p.endswith(".json")
            return json.loads(frozen[p])
        for item in inv["replays"]:
            then = time.monotonic()
            result = getattr(research, item["function"])(load)
            actual = encoded(result)
            assert actual == frozen[item["payload"]], item["function"]
            comparisons.append({"function": item["function"], "byte_identical": True,
                                "sha256": digest(actual), "seconds": time.monotonic() - then})
    finally:
        guard_active[0] = False
    for p, b in frozen.items():
        assert read(p) == b, p
    assert current_membership() == before_membership
    for p, b in control_bytes.items():
        assert (read(p) if (ROOT / p).exists() else None) == b, p
    assert {p: read(p) for p in CONTEXT} == context_before
    receipt = {
        "status": "PASS", "iteration": 180, "prevalidation": prevalidate,
        "owned": len(inv["owned"]), "strict_external": len(inv["external"]), "contexts": 4,
        "inventory_sha256": digest(inv_bytes), "report_sha256": digest(frozen[REPORT]),
        "verifier_sha256": digest(frozen[PREFIX + "verify180.py"]),
        "seal_sha256": None if prevalidate else digest(control_bytes[CONTROLS[2]]),
        "comparisons": comparisons, "probes": probes,
        "context_current": {p: digest(b) for p, b in context_before.items()},
        "context_inherited_drift": [p for p in CONTEXT if digest(context_before[p]) !=
                                    next(e["sha256"] for e in inv["context"] if e["path"] == p)],
        "before_after": "Strict bytes, controls, complete owned/ancestor/parent membership and current contexts unchanged",
        "limits": "Python audit guard, not an OS sandbox; clean-clone reconstruction not tested",
        "runtime_seconds": time.monotonic() - start,
    }
    return receipt


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert sys.argv[1:] in ([], ["--prevalidate"])
    sys.stdout.buffer.write(encoded(verify(bool(sys.argv[1:]))))
