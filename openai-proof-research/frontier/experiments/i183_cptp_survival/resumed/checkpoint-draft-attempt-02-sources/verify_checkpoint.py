"""Read-only verification of an INCOMPLETE, UNSEALED I183 checkpoint.

This is not the final 23-stage verifier and cannot authorize a seal.
The authenticated modules are loaded from immutable byte buffers.
"""
import hashlib
import fractions
import itertools
import json
import math
import os
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "frontier/experiments/i183_cptp_survival/resumed"
SOURCES = "frontier/sources/i183_cptp_survival/resumed"
REPORT = "frontier/iterations/i183-cptp-survival-resumed.md"
INVENTORY = BASE + "/checkpoint-inventory.json"
CONTEXT = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md")
EXECUTABLE = {BASE + "/" + x for x in
              ("auth.py", "exact.py", "indexed.py", "incidences.py", "proof_checks.py")}


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
    assert draft or not sys.argv[1:]
    if draft:
        assert not path_of(INVENTORY).exists()
        inventory_bytes = json.dumps({
            "status": "INCOMPLETE_UNSEALED_CHECKPOINT",
            "owned": [record(p) for p in membership()],
            "controls": [],
        }, sort_keys=True, indent=2).encode()
    else:
        inventory_bytes = path_of(INVENTORY).read_bytes()
    inventory = json.loads(inventory_bytes)
    assert inventory["status"] == "INCOMPLETE_UNSEALED_CHECKPOINT"
    assert inventory["controls"] == ([] if draft else [INVENTORY])
    owned = {x["path"]: x for x in inventory["owned"]}
    assert len(owned) == len(inventory["owned"])
    declared = sorted(set(owned) | set(inventory["controls"]))
    assert membership() == declared
    for item in owned.values():
        assert record(item["path"]) == item
    frozen = json.loads(path_of(BASE + "/inputs.json").read_bytes())
    strict = {x["path"]: x for x in frozen["strict"]}
    assert len(strict) == len(frozen["strict"]) == 1067
    assert set(CONTEXT) == {x["path"] for x in frozen["context"]}
    for item in strict.values():
        assert record(item["path"]) == item
    contexts = [record(p) for p in CONTEXT]
    # Immutable, authenticated sources only. Older code is never compiled.
    buffers = {p: path_of(p).read_bytes() for p in EXECUTABLE}
    for p, data in buffers.items():
        assert digest(data) == owned[p]["sha256"]
    allowed_reads = {str(path_of(p)) for p in set(owned) | set(strict) |
                     set(CONTEXT) | {INVENTORY}}
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
    load_owned(BASE + "/indexed.py", exact)
    load_owned(BASE + "/incidences.py", exact)
    load_owned(BASE + "/proof_checks.py", exact)

    def read_json(path):
        assert path in strict
        data = path_of(path).read_bytes()
        assert digest(data) == strict[path]["sha256"]
        return json.loads(data)

    def canonical(obj):
        return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()

    runtimes = {}
    for name, call in (("unit", exact["unit_tests"]),
                       ("indexed", lambda: exact["indexed"](read_json)),
                       ("incidences", exact["incidence_tests"]),
                       ("proof", exact["proof_checks"])):
        t = time.monotonic()
        actual = call()
        runtimes[name] = time.monotonic() - t
        saved = json.loads(path_of(BASE + "/" + name + "-attempt-01.json").read_bytes())
        assert canonical(actual) == canonical(saved), name
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
    if not draft:
        assert path_of(INVENTORY).read_bytes() == inventory_bytes
    assert membership() == declared
    assert [record(p) for p in CONTEXT] == contexts
    print(json.dumps({
        "status": "PASS_INCOMPLETE_CHECKPOINT_ONLY",
        "draft_inventory": draft,
        "sealed": False, "prevalidated_for_seal": False,
        "mandatory_stage_prefix_recomputed": 12, "mandatory_stages_required": 23,
        "full_mandatory_replay": False,
        "remaining_stages": exact["ALL_STAGES"][12:],
        "strict": len(strict), "owned": len(owned),
        "contexts_current": contexts, "eight_live_probes": outcomes,
        "forgery_positive_control": True,
        "report_sha256": owned[REPORT]["sha256"],
        "verifier_sha256": owned[BASE + "/verify_checkpoint.py"]["sha256"],
        "checkpoint_inventory_sha256": digest(inventory_bytes),
        "replay_seconds": runtimes, "total_seconds": time.monotonic() - start,
        "limits": ["Python audit hook, not an OS sandbox",
                   "Clean-clone reconstruction untested",
                   "Indexed arc geometry only degree-checked",
                   "No universal E183 proof or refutation"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
