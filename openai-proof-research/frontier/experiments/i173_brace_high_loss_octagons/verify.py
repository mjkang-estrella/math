"""I173 immutable-first verifier. No ancestor executable is loaded."""
import hashlib
import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time
import types
# Warm every dependency used by bound source before activating the read guard.
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd

ROOT = Path(__file__).resolve().parents[3]
EXP = "frontier/experiments/i173_brace_high_loss_octagons/"
SRC = "frontier/sources/i173_brace_high_loss_octagons/"
REPORT = "frontier/iterations/i173-brace-high-loss-octagons.md"
CONTROL = {EXP + x for x in ("inventory.json", "prevalidation.json", "seal.json")}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def actual_owned():
    paths = {REPORT}
    for folder in (EXP, SRC):
        paths.update(str(p.relative_to(ROOT)) for p in (ROOT / folder).rglob("*") if p.is_file())
    return paths - CONTROL


def bound_memory(inv):
    assert actual_owned() == {r["path"] for r in inv["owned"]}, "owned inventory differs"
    memory = {}
    for row in inv["owned"] + inv["external"]:
        path = ROOT / row["path"]
        assert not path.is_symlink(), row["path"]
        raw = path.read_bytes()
        assert sha(raw) == row["sha256"] and len(raw) == row["size"], row["path"]
        memory[row["path"]] = raw
    return types.MappingProxyType(memory)


def context_receipts(inv):
    return [dict(path=r["path"], expected=r["sha256"],
                 actual=sha((ROOT / r["path"]).read_bytes()),
                 drift=sha((ROOT / r["path"]).read_bytes()) != r["sha256"])
            for r in inv["context"]]


def run(prevalidate=False):
    start = time.monotonic()
    inventory_bytes = (ROOT / (EXP + "inventory.json")).read_bytes()
    inv = json.loads(inventory_bytes)
    memory = bound_memory(inv)
    before_contexts = context_receipts(inv)
    if prevalidate:
        assert not (ROOT / (EXP + "seal.json")).exists(), "prevalidation requires unsealed package"
    else:
        sealraw = (ROOT / (EXP + "seal.json")).read_bytes()
        seal = json.loads(sealraw)
        assert seal["inventory_sha256"] == sha(inventory_bytes)
        preraw = (ROOT / (EXP + "prevalidation.json")).read_bytes()
        assert sha(preraw) == seal["prevalidation_sha256"]
        pre = json.loads(preraw)
        assert pre["status"] == "PASS" and pre["inventory_sha256"] == sha(inventory_bytes)
        assert seal["report_sha256"] == sha(memory[REPORT])
        assert seal["verifier_sha256"] == sha(memory[EXP + "verify.py"])
    active = False
    allowed_code = set()
    sources = {str(ROOT / (EXP + name + ".py")): memory[EXP + name + ".py"]
               for name in inv["modules"]}
    alien = compile("pass", "<I173-unowned-exec-probe>", "exec")

    def guard(event, args):
        if not active:
            return
        if event == "open":
            raise PermissionError("I173: no filesystem reads or writes during diagnostics")
        if event.startswith(("socket.", "subprocess.", "ctypes.")) or event in {
            "os.system", "os.fork", "os.posix_spawn", "os.exec", "os.spawn",
            "os.remove", "os.rmdir", "os.rename", "os.mkdir", "os.chmod",
            "os.chown", "os.link", "os.symlink", "os.truncate", "os.utime",
            "os.listdir", "os.scandir",
        }:
            raise PermissionError("I173: forbidden effect " + event)
        if event == "compile":
            raw, filename = args
            raw = raw.encode() if isinstance(raw, str) else raw
            if filename not in sources or raw != sources[filename]:
                raise PermissionError("I173: unbound or forged compilation")
        if event == "exec" and id(args[0]) not in allowed_code:
            raise PermissionError("I173: unapproved executable")

    sys.addaudithook(guard)
    probes, comparisons = [], []
    active = True
    try:
        tests = [
            ("write", lambda: open(str(ROOT / (EXP + "guard-never-created")), "wb")),
            ("mutation", lambda: os.mkdir(str(ROOT / (EXP + "guard-never-created-dir")))),
            ("network", lambda: socket.socket()),
            ("subprocess", lambda: subprocess.Popen(["/bin/true"])),
            ("unbound-read", lambda: open(str(ROOT / "AGENTS.md"), "rb")),
            ("outside-compile", lambda: compile("pass", "<I173-outsider>", "exec")),
            ("outside-exec", lambda: exec(alien, {})),
            ("forged-owned-source", lambda: compile(b"pass\n", str(ROOT / (EXP + "toolkit.py")), "exec")),
        ]
        for label, probe in tests:
            try:
                probe()
            except PermissionError:
                probes.append(dict(probe=label, blocked=True))
            else:
                raise AssertionError("Guard probe not blocked: " + label)
        for name in inv["modules"]:
            module = types.ModuleType(name)
            sys.modules[name] = module
            filename = str(ROOT / (EXP + name + ".py"))
            code = compile(sources[filename], filename, "exec")
            allowed_code.add(id(code))
            exec(code, module.__dict__)
        research = sys.modules["research"]
        research.DATA = memory
        for job in inv["replays"]:
            begin = time.monotonic()
            result = getattr(research, job["function"])()
            raw = encoded(result)
            assert raw == memory[job["payload"]], job["payload"]
            comparisons.append(dict(function=job["function"], payload=job["payload"],
                                    sha256=sha(raw), byte_identical=True,
                                    seconds=round(time.monotonic() - begin, 6)))
    finally:
        active = False
    # Full outer rehash, including all non-context external bytes, after replay.
    after = bound_memory(inv)
    assert dict(after) == dict(memory)
    after_contexts = context_receipts(inv)
    assert before_contexts == after_contexts, "context changed during replay"
    receipt = dict(status="PASS", iteration=173, prevalidation=prevalidate,
                   inventory_sha256=sha(inventory_bytes), comparisons=comparisons, probes=probes,
                   owned_count=len(inv["owned"]), non_context_external_count=len(inv["external"]),
                   before_after="all owned and mathematical external bindings identical",
                   contexts=before_contexts, report_sha256=sha(memory[REPORT]),
                   verifier_sha256=sha(memory[EXP + "verify.py"]),
                   python_version=sys.version,
                   runtime_seconds=round(time.monotonic() - start, 6),
                   limits="Python audit guard, not OS sandbox; no clean-clone test")
    if not prevalidate:
        assert (ROOT / (EXP + "seal.json")).read_bytes() == sealraw
        assert (ROOT / (EXP + "prevalidation.json")).read_bytes() == preraw
        assert (ROOT / (EXP + "inventory.json")).read_bytes() == inventory_bytes
        receipt["seal_sha256"] = sha(sealraw)
    return receipt


if __name__ == "__main__":
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert not sys.argv[1:] or prevalidate
    receipt = run(prevalidate)
    if prevalidate:
        with (ROOT / (EXP + "prevalidation.json")).open("xb") as out:
            out.write(encoded(receipt))
    print(json.dumps(receipt, sort_keys=True, indent=2))
