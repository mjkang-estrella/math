"""I172 immutable-first replay. All diagnostic inputs are authenticated bytes."""
import collections
import fractions
import functools
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

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SOURCE = ROOT / "frontier/sources/i172_prescribed_square_switch"
REPORT = ROOT / "frontier/iterations/i172-prescribed-square-switch.md"
CONTROLS = {"inventory.json", "prevalidation.json", "seal.json"}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"))+"\n").encode()


def main():
    started = time.perf_counter()
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert prevalidate or not sys.argv[1:]
    inventory_bytes = (HERE / "inventory.json").read_bytes()
    inventory = json.loads(inventory_bytes)
    seal_bytes = None
    if not prevalidate:
        seal_bytes = (HERE / "seal.json").read_bytes()
        seal = json.loads(seal_bytes)
        assert seal["inventory_sha256"] == sha(inventory_bytes)
        pre = (HERE / "prevalidation.json").read_bytes()
        assert seal["prevalidation_sha256"] == sha(pre)
        assert json.loads(pre)["status"] == "PASS"
        assert seal["report_sha256"] == sha(REPORT.read_bytes())
        assert seal["verifier_sha256"] == sha(Path(__file__).read_bytes())
    else:
        assert not (HERE / "seal.json").exists(), "prevalidation only before initial seal"
    owned = {e["path"] for e in inventory["owned"]}
    actual = {str(p.relative_to(ROOT)) for directory in (HERE, SOURCE)
              for p in directory.rglob("*") if p.is_file()
              and not (p.parent == HERE and p.name in CONTROLS)}
    actual.add(str(REPORT.relative_to(ROOT)))
    assert actual == owned, ("inventory incomplete", actual-owned, owned-actual)
    bound = {}
    contexts = []
    for entry in inventory["owned"]+inventory["external"]:
        p = ROOT / entry["path"]
        data = p.read_bytes()
        ok = len(data) == entry["size"] and sha(data) == entry["sha256"]
        if entry.get("role") == "context-only":
            contexts.append(dict(path=entry["path"], match=ok,
                                 expected_sha256=entry["sha256"], actual_sha256=sha(data)))
        else:
            assert ok, entry["path"]
            bound[entry["path"]] = data
    diagnostic_paths = [str((HERE / name).relative_to(ROOT))
                        for name in ("toolkit.py", "research.py", "attacks.py")]
    sources = {str(ROOT / name): bound[name] for name in diagnostic_paths}
    known_codes = set()
    outside_code = compile("1 + 1", "/outside-I172-probe.py", "exec")
    probes = []

    def guard(event, args):
        if event == "open":
            _, mode, flags = args
            if (mode is not None and any(c in mode for c in "wax+")) or (
                flags is not None and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
            ):
                raise PermissionError("I172 writes forbidden")
            # Every data byte is already in bound; there is no trusted-path
            # exemption and hence no path-to-byte TOCTOU gap during diagnostics.
            raise PermissionError("I172 filesystem reads forbidden; use bound memory")
        if event in {"os.remove", "os.rename", "os.rmdir", "os.mkdir", "os.chmod",
                     "os.chown", "os.truncate", "os.utime", "os.link", "os.symlink",
                     "os.chdir", "os.putenv", "os.unsetenv"}:
            raise PermissionError("I172 mutation forbidden")
        if event.startswith("socket.") or event.startswith("http."):
            raise PermissionError("I172 network forbidden")
        if event.startswith("subprocess.") or event in {"os.system", "os.fork", "os.posix_spawn", "os.exec"}:
            raise PermissionError("I172 subprocess forbidden")
        if event == "compile":
            data, filename = args
            if isinstance(data, str):
                data = data.encode()
            if filename not in sources or data != sources[filename]:
                raise PermissionError("I172 source bytes not authenticated")
        if event == "exec" and args[0] not in known_codes:
            raise PermissionError("I172 outside code execution forbidden")

    sys.addaudithook(guard)

    def blocked(label, function):
        try:
            function()
        except PermissionError:
            probes.append(dict(probe=label, blocked=True))
        else:
            raise AssertionError("unguarded "+label)

    blocked("write", lambda: open(str(HERE / "forbidden-probe"), "w"))
    blocked("mutation", lambda: os.mkdir(str(HERE / "forbidden-directory")))
    blocked("network", lambda: socket.socket())
    blocked("subprocess", lambda: subprocess.Popen(["/bin/true"]))
    blocked("unbound-read", lambda: open(str(ROOT / "UNBOUND-I172-PROBE"), "rb"))
    blocked("outside-compile", lambda: compile("1", "/outside-I172-probe.py", "exec"))
    blocked("outside-exec", lambda: exec(outside_code, {}))
    first_path = next(iter(sources))
    blocked("forged-owned-source", lambda: compile(sources[first_path]+b"\n# forged\n", first_path, "exec"))

    def load(path):
        if path not in bound:
            raise PermissionError("I172 unbound memory input: "+path)
        return json.loads(bound[path])

    env = dict(load=load, __name__="i172")
    for path, data in sources.items():
        # Compile receives the authenticated bytes, not a fresh filesystem read.
        code = compile(data, path, "exec")
        known_codes.add(code)
        exec(code, env)
    comparisons = []
    for replay in inventory["replays"]:
        start = time.perf_counter()
        print("I172 replay "+replay["function"], file=sys.stderr, flush=True)
        result = encoded(env[replay["function"]]())
        assert result == bound[replay["payload"]], replay["payload"]
        comparisons.append(dict(function=replay["function"], payload=replay["payload"],
                                match=True, sha256=sha(result),
                                seconds=round(time.perf_counter()-start, 6)))
    # Bytes stay immutable in memory throughout diagnostics. The outer control
    # caller separately checks current bindings after replay, without relaxing
    # the in-process read guard.
    receipt = dict(status="PASS", iteration=172, prevalidation=prevalidate,
                   comparisons=comparisons, probes=probes, contexts=contexts,
                   owned_count=len(inventory["owned"]),
                   non_context_external_count=sum(e.get("role") != "context-only"
                                                  for e in inventory["external"]),
                   input_policy="authenticated immutable bytes; all runtime filesystem reads blocked",
                   report_sha256=sha(bound[str(REPORT.relative_to(ROOT))]),
                   verifier_sha256=sha(bound[str(Path(__file__).relative_to(ROOT))]),
                   inventory_sha256=sha(inventory_bytes),
                   seal_sha256=sha(seal_bytes) if seal_bytes else None,
                   runtime_seconds=round(time.perf_counter()-started, 6))
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
