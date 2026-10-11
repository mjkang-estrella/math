"""I167 immutable-first verifier; stdout only, standard library, -I -B."""
import hashlib
import json
import os
import ast
import collections
import fractions
import functools
import itertools
import math
import pkgutil
from pathlib import Path
import runpy
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i167_exchange_step_braces"
REPORT = ROOT / "frontier/iterations/i167-exchange-step-braces.md"
CONTROLS = {HERE / name for name in ("owned-files.json", "prevalidation.json", "seal.json")}
CONTEXT = {"frontier/TEN-FINDINGS.md", "frontier/iterations/README.md"}
EXECUTABLES = {HERE / name for name in ("kernel.py", "diagnostics.py", "support.py", "reduction_audit.py")}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory_paths():
    return {p for base in (HERE, SOURCE) for p in base.rglob("*") if p.is_file()} | {REPORT}


def validate_bytes():
    inventory = json.loads((HERE / "owned-files.json").read_text())
    owned = {ROOT / row["path"] for row in inventory["files"]}
    assert inventory_paths()-CONTROLS == owned, "owned inventory mismatch"
    for row in inventory["files"]:
        p = ROOT / row["path"]
        assert not p.is_symlink() and p.is_file()
        assert p.stat().st_size == row["size"] and digest(p) == row["sha256"], row["path"]
    policy = json.loads((SOURCE / "replay-policy.json").read_text())
    assert set(policy["context_only_exclusions"]) == CONTEXT
    assert {ROOT / p for p in policy["allowed_execution"]} == EXECUTABLES
    bindings = json.loads((SOURCE / "external-bindings.json").read_text())
    external = set()
    for row in bindings["files"]:
        if row["path"] in CONTEXT:
            continue
        p = ROOT / row["path"]
        assert not p.is_symlink() and p.is_file()
        assert p.stat().st_size == row["size"] and digest(p) == row["sha256"], row["path"]
        external.add(p)
    assert len(external) == 68
    original = ROOT / "frontier/iterations/i166-affine-span-braces.md"
    original_seal = ROOT / "frontier/experiments/i166_affine_span_braces/seal.json"
    assert digest(original) == "b85346fd77aca2a38bcbdb9e29d10fbb5c6b025e42fb16e7ff1777b61ef1b7ec"
    assert digest(original_seal) == "8e080e006b78700ad4487adb569fabf236fd96f8fba615376d5260dd02a4c717"
    paper = (ROOT / "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex").read_bytes()
    assert hashlib.sha1(b"blob "+str(len(paper)).encode()+b"\0"+paper).hexdigest() == \
           "01dd9e0c56b84f77c2051379e1202821bc2164cd"
    return owned | external, len(owned)


def readonly_guard(verified):
    stdroot = Path(sys.base_prefix).resolve()
    ownexec = {p.resolve() for p in EXECUTABLES}
    readable = {p.resolve() for p in verified}
    def hook(event, args):
        if event == "open":
            path, mode, flags = args
            assert not (isinstance(mode, str) and any(c in mode for c in "wax+")), "write blocked"
            assert not (flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)), "write blocked"
            if isinstance(path, (str, bytes)):
                p = Path(os.fsdecode(path)).resolve()
                assert p in readable or p.is_relative_to(stdroot), ("unbound read", str(p))
        if event == "exec":
            filename = args[0].co_filename
            if filename.startswith("<frozen "):
                return
            p = Path(filename).resolve()
            assert p in ownexec or p.is_relative_to(stdroot), ("unowned execution", filename)
        if event.startswith(("socket.", "subprocess.", "ctypes.")) or event in {
            "os.system", "os.fork", "os.forkpty", "os.posix_spawn", "os.exec",
            "os.spawn", "os.remove", "os.rename", "os.rmdir", "os.mkdir",
            "os.link", "os.symlink", "os.truncate", "os.chmod", "os.chown",
            "os.utime", "os.putenv", "os.unsetenv", "shutil.copyfile"
        }:
            raise AssertionError(("forbidden side effect", event))
    sys.addaudithook(hook)


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode, "use python3 -I -B"
    start = time.monotonic()
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    assert prevalidate or not sys.argv[1:]
    verified, count = validate_bytes()
    receipt_binding = {
        "inventory_sha256": digest(HERE / "owned-files.json"),
        "external_bindings_sha256": digest(SOURCE / "external-bindings.json"),
        "policy_sha256": digest(SOURCE / "replay-policy.json"),
        "report_sha256": digest(REPORT)
    }
    if not prevalidate:
        seal = json.loads((HERE / "seal.json").read_text())
        assert seal["bindings"] == receipt_binding
        assert seal["prevalidation_sha256"] == digest(HERE / "prevalidation.json")
        previous = json.loads((HERE / "prevalidation.json").read_text())
        assert previous["status"] == "PASS" and previous["bindings"] == receipt_binding
    # pkgutil/collections and Fraction's dependencies are initialized above:
    # stdlib namedtuple bootstrapping uses an eval-generated <string> code
    # object. The diagnostic phase still categorically rejects such execution.
    readonly_guard(verified)
    checks = []
    for script, payload in (("diagnostics.py", "diagnostic-attempt-01.json"),
                            ("support.py", "support-attempt-01.json"),
                            ("reduction_audit.py", "reduction-01.json")):
        expected = json.loads((HERE / payload).read_text())
        actual = runpy.run_path(str(HERE / script))["run"]()
        # JSON normalizes the deliberate tuple edge representation.
        assert json.loads(json.dumps(actual)) == expected, ("payload mismatch", payload)
        checks.append({"script": script, "payload": payload, "status": "PASS"})
    print(json.dumps({"status": "PASS", "mode": "prevalidation" if prevalidate else "sealed replay",
                      "bindings": receipt_binding, "owned_payload_files": count,
                      "immutable_external_files": 68, "context_exclusions": sorted(CONTEXT),
                      "checks": checks, "read_only": True, "ancestor_execution": False,
                      "seconds": round(time.monotonic()-start, 3)}, indent=2))


if __name__ == "__main__":
    main()
