"""Full bounded finalization verifier, adapted from same-I183 checkpoint.

Authenticates complete membership and bytes before and after all 23 stages.
The audit hook is a Python guard, not an operating-system sandbox.
"""
import hashlib
import fractions
import collections
import itertools
import json
import math
import os
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
BASE = "frontier/experiments/i183_cptp_finalization"
SOURCES = "frontier/sources/i183_cptp_finalization"
REPORT = "frontier/iterations/i183-cptp-finalization.md"
INVENTORY = BASE + "/inventory.json"
PREVALIDATION = BASE + "/prevalidation.json"
PRE_STDERR = BASE + "/prevalidation.stderr"
SEAL = BASE + "/seal.json"
CONTROLS = [INVENTORY, PREVALIDATION, PRE_STDERR, SEAL]
CONTEXT = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md")
EXECUTABLE = {BASE + "/" + x for x in
              ("auth.py", "exact.py", "geometry.py", "indexed.py", "stages.py",
               "fiveport.py", "tail.py", "mandatory.py", "incidences.py", "proof_checks.py")}


class Blocked(RuntimeError):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def path_of(path):
    p = Path(path)
    assert not p.is_absolute() and ".." not in p.parts
    full = ROOT / p
    assert full.resolve().is_relative_to(ROOT)
    return full


def record(path):
    data = path_of(path).read_bytes()
    return {"path": path, "size": len(data), "sha256": digest(data)}


def membership():
    out = {REPORT}
    for directory in (BASE, SOURCES):
        for p in path_of(directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                out.add(p.relative_to(ROOT).as_posix())
    return sorted(out)


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode
    start = time.monotonic()
    draft = sys.argv[1:] == ["--draft"]
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert draft or prevalidate or not sys.argv[1:]
    control_bytes = {}
    if draft:
        assert not path_of(INVENTORY).exists()
        inventory_bytes = json.dumps({
            "status": "I183_BOUNDED_FINALIZATION",
            "owned": [record(p) for p in membership()],
            "controls": [],
        }, sort_keys=True, indent=2).encode()
    else:
        inventory_bytes = path_of(INVENTORY).read_bytes()
    inventory = json.loads(inventory_bytes)
    assert inventory["status"] == "I183_BOUNDED_FINALIZATION"
    assert inventory["controls"] == ([] if draft else CONTROLS)
    owned = {x["path"]: x for x in inventory["owned"]}
    assert len(owned) == len(inventory["owned"])
    if prevalidate:
        assert not path_of(SEAL).exists()
        assert path_of(PREVALIDATION).read_bytes() == b""
        assert path_of(PRE_STDERR).read_bytes() == b""
    active_controls = ([] if draft else
                       [p for p in CONTROLS if p != SEAL or not prevalidate])
    declared = sorted(set(owned) | set(active_controls))
    assert membership() == declared
    for item in owned.values():
        assert record(item["path"]) == item
    if not draft:
        control_bytes = {p:path_of(p).read_bytes() for p in active_controls}
        assert control_bytes[INVENTORY] == inventory_bytes
    if not draft and not prevalidate:
        seal = json.loads(control_bytes[SEAL])
        pre = json.loads(control_bytes[PREVALIDATION])
        assert seal["status"] == "SEALED_I183_BOUNDED_FINALIZATION"
        assert seal["inventory_sha256"] == digest(inventory_bytes)
        assert seal["prevalidation_sha256"] == digest(control_bytes[PREVALIDATION])
        assert seal["prevalidation_stderr_sha256"] == digest(control_bytes[PRE_STDERR])
        assert control_bytes[PRE_STDERR] == b""
        assert pre["status"] == "PASS_PREVALIDATION_23_STAGES"
        assert pre["inventory_sha256"] == digest(inventory_bytes)
        assert seal["report_sha256"] == pre["report_sha256"] == owned[REPORT]["sha256"]
        assert seal["verifier_sha256"] == pre["verifier_sha256"] == owned[
            BASE + "/verify.py"]["sha256"]
        assert seal["mandatory_payload_sha256"] == pre["mandatory_payload_sha256"] == owned[
            BASE + "/mandatory-01.json"]["sha256"]
        assert pre["full_mandatory_replay"] and pre["mandatory_stages_recomputed"] == 23
        assert pre["forgery_positive_control"] and len(pre["eight_live_probes"]) == 8
        assert all(p["status"] == "BLOCKED" for p in pre["eight_live_probes"])
    frozen = json.loads(path_of(BASE + "/inputs.json").read_bytes())
    strict = {x["path"]: x for x in frozen["strict"]}
    assert len(strict) == len(frozen["strict"]) == 1153
    assert set(CONTEXT) == {x["path"] for x in frozen["context"]}
    for item in strict.values():
        assert record(item["path"]) == item
    contexts = [record(p) for p in CONTEXT]
    # Immutable, authenticated sources only. Older code is never compiled.
    buffers = {p: path_of(p).read_bytes() for p in EXECUTABLE}
    for p, data in buffers.items():
        assert digest(data) == owned[p]["sha256"]
    allowed_reads = {str(path_of(p)) for p in set(owned) | set(strict) |
                     set(CONTEXT) | set(active_controls)}
    authorized_codes = set()

    def authenticate_source(path, data):
        if path not in buffers or digest(data) != owned[path]["sha256"]:
            raise Blocked("unauthenticated executable source")
        if data != buffers[path]:
            raise Blocked("source differs from authenticated buffer")

    def hook(event, args):
        if event == "open":
            name, mode, flags = args
            if flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT |
                        os.O_TRUNC | os.O_APPEND):
                raise Blocked("write")
            if not isinstance(name, (str, bytes, os.PathLike)):
                raise Blocked("unbound descriptor read")
            if os.path.realpath(os.fsdecode(name)) not in allowed_reads:
                raise Blocked("unbound read")
        elif event in {"os.remove", "os.rename", "os.rmdir", "os.mkdir",
                       "os.link", "os.symlink", "os.chmod", "os.chown",
                       "os.truncate", "os.utime", "os.chdir", "os.system",
                       "os.fork", "os.forkpty", "os.posix_spawn"}:
            raise Blocked("mutation or process")
        elif event.startswith("socket.") or event == "subprocess.Popen":
            raise Blocked("network or subprocess")
        elif event == "compile":
            source, name = args
            try:
                relative = Path(name).relative_to(ROOT).as_posix()
            except (ValueError, TypeError):
                raise Blocked("outside compilation")
            if isinstance(source, str):
                source = source.encode()
            authenticate_source(relative, source)
        elif event == "exec" and args[0] not in authorized_codes:
            raise Blocked("outside execution")

    # Probe code created BEFORE installation; execution must still be rejected.
    outside_code = compile("outside_marker = True", "<outside-probe>", "exec")
    sys.addaudithook(hook)

    def load_owned(path, ns=None):
        data = buffers[path]
        authenticate_source(path, data)
        code = compile(data, str(path_of(path)), "exec")
        authorized_codes.add(code)
        if ns is None:
            ns = {"__name__": "checkpoint_owned", "__file__": str(path_of(path))}
        exec(code, ns)
        return ns

    auth = load_owned(BASE + "/auth.py")
    assert auth["check"]() == contexts
    exact = load_owned(BASE + "/exact.py")
    for name in ("geometry.py", "indexed.py", "stages.py", "fiveport.py", "tail.py",
                 "mandatory.py", "incidences.py", "proof_checks.py"):
        load_owned(BASE + "/" + name, exact)

    def read_json(path):
        assert path in strict
        data = path_of(path).read_bytes()
        assert digest(data) == strict[path]["sha256"]
        return json.loads(data)

    def canonical(obj):
        return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()

    runtimes = {}
    for name, call in (("mandatory", lambda: exact["mandatory"](read_json)),
                       ("unit", exact["unit_tests"]),
                       ("incidences", exact["incidence_tests"]),
                       ("proof", exact["proof_checks"])):
        t = time.monotonic()
        actual = call()
        runtimes[name] = time.monotonic() - t
        saved = json.loads(path_of(BASE + "/" + name + "-01.json").read_bytes())
        assert canonical(actual) == canonical(saved), name
        if name == "mandatory":
            assert actual["order"] == exact["ALL_STAGES"] and len(actual["order"]) == 23
    assert len(exact["ALL_STAGES"]) == 23
    assert exact["ALL_STAGES"][:12] == exact["ORDER"]

    source_path = BASE + "/exact.py"
    # Positive control makes the forgery check non-vacuous.
    authenticate_source(source_path, buffers[source_path])
    forged = buffers[source_path] + b"\n# forged checkpoint probe\n"
    assert digest(forged) != owned[source_path]["sha256"]
    probes = [
        ("write", lambda: open(str(path_of(BASE + "/probe.tmp")), "wb")),
        ("mutation", lambda: os.remove(str(path_of(BASE + "/nonexistent-probe")))),
        ("network", lambda: socket.socket(socket.AF_INET, socket.SOCK_STREAM)),
        ("subprocess", lambda: subprocess.Popen([sys.executable, "-I", "-B", "-c", "pass"])),
        ("unbound-read", lambda: open(str(ROOT / "i183-unbound-probe"), "rb")),
        ("outside-compile", lambda: compile("pass", "<outside>", "exec")),
        ("outside-exec", lambda: exec(outside_code, {})),
        ("forged-owned-source", lambda: compile(forged, str(path_of(source_path)), "exec")),
    ]
    outcomes = []
    for name, fn in probes:
        try:
            fn()
        except Blocked:
            outcomes.append({"probe": name, "status": "BLOCKED"})
        else:
            raise AssertionError("probe not blocked: " + name)
    assert len(outcomes) == 8
    assert auth["check"]() == contexts
    for item in list(strict.values()) + list(owned.values()):
        assert record(item["path"]) == item
    for path,data in control_bytes.items():
        assert path_of(path).read_bytes() == data
    assert membership() == declared
    assert [record(p) for p in CONTEXT] == contexts
    print(json.dumps({
        "status": ("PASS_DRAFT_23_STAGES" if draft else
                   "PASS_PREVALIDATION_23_STAGES" if prevalidate else
                   "PASS_SEALED_23_STAGES"),
        "draft_inventory": draft,
        "sealed": not draft and not prevalidate,
        "mandatory_stages_recomputed": 23, "mandatory_stages_required": 23,
        "full_mandatory_replay": True, "order": exact["ALL_STAGES"],
        "strict": len(strict), "owned": len(owned),
        "contexts_current": contexts, "eight_live_probes": outcomes,
        "forgery_positive_control": True,
        "report_sha256": owned[REPORT]["sha256"],
        "verifier_sha256": owned[BASE + "/verify.py"]["sha256"],
        "inventory_sha256": digest(inventory_bytes),
        "mandatory_payload_sha256": owned[BASE + "/mandatory-01.json"]["sha256"],
        "seal_sha256": digest(control_bytes[SEAL]) if SEAL in control_bytes else None,
        "replay_seconds": runtimes, "total_seconds": time.monotonic() - start,
        "limits": ["Python audit hook, not an OS sandbox",
                   "Clean-clone reconstruction untested",
                   "Historical first two resumed freeze sources were not preserved",
                   "No universal E183 proof or refutation"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
