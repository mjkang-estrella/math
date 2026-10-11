"""Immutable-byte read-only replay. An audit guard, explicitly not an OS sandbox."""
import ast
import builtins
import hashlib
import io
import itertools
import functools
import json
import math
import os
import socket
import subprocess
import sys
import time
import types
from fractions import Fraction
from pathlib import Path
from types import MappingProxyType

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
REL = "frontier/experiments/i179_path_recombination/"
REPORT = "frontier/iterations/i179-path-recombination.md"
CONTEXTS = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
            "frontier/iterations/README.md"}
CONTROLS = {REL+n for n in ("inventory.json", "prevalidation.json", "seal.json")}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def encoding(value):
    def default(x):
        if isinstance(x, Fraction):
            return str(x)
        raise TypeError(type(x).__name__)
    return (json.dumps(value, indent=2, sort_keys=True, default=default)+"\n").encode()


def membership():
    files = {REPORT}
    for folder in (HERE, ROOT / "frontier/sources/i179_path_recombination"):
        files.update(str(p.relative_to(ROOT)) for p in folder.rglob("*") if p.is_file())
    return files


def main():
    start = time.monotonic()
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert not sys.argv[1:] or prevalidate
    invbytes = (HERE / "inventory.json").read_bytes()
    inv = json.loads(invbytes)
    assert set(inv["controls"]) == CONTROLS
    assert {x["path"] for x in inv["context"]} == CONTEXTS
    rows = inv["owned"]+inv["external"]
    assert len(rows) == len({x["path"] for x in rows})
    assert not {x["path"] for x in rows} & (CONTROLS | CONTEXTS)
    frozen = {}
    for row in rows:
        b = (ROOT / row["path"]).read_bytes()
        assert digest(b) == row["sha256"] and len(b) == row["size"], row["path"]
        frozen[row["path"]] = b
    blobs = MappingProxyType(frozen)
    before_membership = membership()
    live_controls = {p: (ROOT / p).read_bytes() for p in CONTROLS if (ROOT / p).exists()}
    assert before_membership == {x["path"] for x in inv["owned"]} | set(live_controls)
    context = {p: (ROOT / p).read_bytes() for p in CONTEXTS}
    inputs = json.loads(blobs[REL+"inputs.json"])
    extra = json.loads(blobs[REL+"supplement.json"])
    assert extra["original_inputs_sha256"] == digest(blobs[REL+"inputs.json"])
    assert inv["external"] == sorted(inputs["strict"]+extra["strict"], key=lambda x: x["path"])
    # Authenticate ancestor chain without parsing, compiling, or executing its Python.
    old = "frontier/experiments/i178_five_port_annihilator/"
    oi = json.loads(blobs[old+"inventory.json"])
    op = json.loads(blobs[old+"prevalidation.json"])
    seal = json.loads(blobs[old+"seal.json"])
    assert (len(oi["owned"]), len(oi["external"]), len(oi["context"])) == (81, 678, 4)
    assert json.loads(blobs[old+"inputs.json"])["strict"] == oi["external"]
    assert seal["inventory_sha256"] == op["inventory_sha256"] == digest(blobs[old+"inventory.json"])
    assert seal["prevalidation_sha256"] == digest(blobs[old+"prevalidation.json"])
    assert op["status"] == "PASS"
    assert {x["path"] for x in oi["context"]} == CONTEXTS
    for p, h in inputs["detached_anchors"].items():
        assert digest(blobs[p]) == h
    for row in oi["owned"]+oi["external"]:
        assert digest(blobs[row["path"]]) == row["sha256"]
    old_membership = {"frontier/iterations/i178-five-port-annihilator.md"}
    for folder in (ROOT / old, ROOT / "frontier/sources/i178_five_port_annihilator"):
        old_membership.update(str(p.relative_to(ROOT)) for p in folder.rglob("*") if p.is_file())
    assert old_membership == {x["path"] for x in oi["owned"]} | set(oi["controls"])
    if prevalidate:
        assert REL+"seal.json" not in live_controls
        assert REL+"prevalidation.json" not in live_controls
    else:
        assert set(live_controls) == CONTROLS
        seal179 = json.loads(live_controls[REL+"seal.json"])
        pre179 = json.loads(live_controls[REL+"prevalidation.json"])
        assert seal179["inventory_sha256"] == digest(invbytes) == pre179["inventory_sha256"]
        assert seal179["prevalidation_sha256"] == digest(live_controls[REL+"prevalidation.json"])
        assert seal179["report_sha256"] == digest(blobs[REPORT])
        assert seal179["verifier_sha256"] == digest(blobs[REL+"verify179.py"])
        assert pre179["status"] == "PASS" and pre179["prevalidation"] is True
        assert all(p["blocked"] for p in pre179["probes"]) and len(pre179["probes"]) == 8
    allowed_source = {str(ROOT / (REL+n)): blobs[REL+n] for n in ("math179.py", "research179.py")}
    outside_code = compile("value = 1", "<unowned>", "exec")
    permitted_code = set()
    guard_active = [True]
    readable = {str(ROOT / p) for p in blobs} | {str(ROOT / p) for p in live_controls} | {
        str(ROOT / p) for p in context}

    def guard(event, args):
        if not guard_active[0]:
            return
        if event == "open":
            path, mode, flags = args
            if isinstance(path, int):
                raise PermissionError("file descriptor access blocked")
            if (mode and any(c in mode for c in "wax+")) or flags & (
                    os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
                raise PermissionError("write blocked")
            if os.path.abspath(os.fsdecode(path)) not in readable:
                raise PermissionError("unbound read blocked")
        elif event in ("os.remove", "os.rename", "os.mkdir", "os.rmdir", "os.link",
                       "os.symlink", "os.chmod", "os.chown", "os.truncate", "os.utime",
                       "os.system", "os.posix_spawn", "subprocess.Popen"):
            raise PermissionError("mutation/process blocked")
        elif event.startswith("socket."):
            raise PermissionError("network blocked")
        elif event == "compile":
            source, filename = args
            if isinstance(source, str):
                source = source.encode()
            if filename not in allowed_source or source != allowed_source[filename]:
                raise PermissionError("unowned or forged source blocked")
        elif event == "exec" and args[0] not in permitted_code:
            raise PermissionError("unowned execution blocked")
    sys.addaudithook(guard)
    probes = []

    def blocked(name, fn):
        try:
            fn()
        except PermissionError:
            probes.append(dict(probe=name, blocked=True))
        else:
            raise AssertionError("probe not blocked: "+name)
    blocked("write", lambda: open(HERE / "forbidden-probe", "w"))
    blocked("mutation", lambda: os.mkdir(HERE / "forbidden-directory"))
    blocked("network", lambda: socket.socket())
    blocked("subprocess", lambda: subprocess.Popen([sys.executable, "-V"]))
    blocked("unbound-read", lambda: open(ROOT / ".i179-unbound", "rb"))
    blocked("outside-compile", lambda: compile("x=1", "<unowned>", "exec"))
    blocked("outside-exec", lambda: exec(outside_code, {}))
    blocked("forged-owned-source", lambda: compile(b"x=1", str(HERE / "math179.py"), "exec"))

    def owned_exec(name, namespace):
        filename = str(HERE / name)
        code = compile(allowed_source[filename], filename, "exec")
        def register(c):
            permitted_code.add(c)
            for x in c.co_consts:
                if isinstance(x, types.CodeType):
                    register(x)
        register(code)
        exec(code, namespace)

    m = types.ModuleType("fresh_math179")
    owned_exec("math179.py", m.__dict__)
    r = {"m": m}
    owned_exec("research179.py", r)
    comparisons = []
    for entry in inv["replays"]:
        ts = time.monotonic()
        payload = encoding(r[entry["function"]](lambda p: json.loads(blobs[p])))
        assert payload == blobs[entry["payload"]], entry["function"]
        comparisons.append(dict(function=entry["function"], byte_identical=True,
                                sha256=digest(payload), seconds=time.monotonic()-ts))
    guard_active[0] = False
    for p, b in blobs.items():
        assert (ROOT / p).read_bytes() == b, p
    for p, b in live_controls.items():
        assert (ROOT / p).read_bytes() == b, p
    for p, b in context.items():
        assert (ROOT / p).read_bytes() == b, p
    assert membership() == before_membership
    now_old = {"frontier/iterations/i178-five-port-annihilator.md"}
    for folder in (ROOT / old, ROOT / "frontier/sources/i178_five_port_annihilator"):
        now_old.update(str(p.relative_to(ROOT)) for p in folder.rglob("*") if p.is_file())
    assert now_old == old_membership
    receipt = dict(
        status="PASS", iteration=179, prevalidation=prevalidate,
        owned=len(inv["owned"]), external=len(inv["external"]), contexts=4,
        inventory_sha256=digest(invbytes), report_sha256=digest(blobs[REPORT]),
        verifier_sha256=digest(blobs[REL+"verify179.py"]),
        seal_sha256=None if prevalidate else digest(live_controls[REL+"seal.json"]),
        comparisons=comparisons, probes=probes,
        context_current={p: digest(b) for p, b in sorted(context.items())},
        before_after="Strict mathematics, controls, full owned/ancestor membership and current contexts unchanged",
        limits="Python audit guard, not an OS sandbox; no clean-clone test",
        runtime_seconds=time.monotonic()-start)
    print(encoding(receipt).decode(), end="")


if __name__ == "__main__":
    main()
