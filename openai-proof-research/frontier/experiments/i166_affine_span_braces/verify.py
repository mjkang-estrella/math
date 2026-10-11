"""Immutable-bytes-first, read-only I166 prevalidation and sealed replay.

Mirrors the I165 protocol: every owned byte (report, experiment payloads,
source bindings) is hash-checked BEFORE any owned diagnostic executes;
the audit hook forbids writes, subprocesses, network, and ancestor code;
the replay recomputes every payload from the owned sources and compares
full JSON equality.  I165 payloads are consumed as data only (hash-bound
in external-bindings.json); I165 code is never executed.
"""
import hashlib
import json
import os
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i166_affine_span_braces"
REPORT = ROOT / "frontier/iterations/i166-affine-span-braces.md"
EXCLUSIONS = {"owned-files.json", "seal.json", "prevalidation.json"}
ALLOWED = {HERE / (name + ".py") for name in
           ("verify", "lib166", "selftest166", "audit_i165", "bracegen",
            "bracediag", "as_check", "survival", "c4reduce", "walk2",
            "census_check")}

I165_DIR = ROOT / "frontier/experiments/i165_square_expansion_multiplicity"
I165_REPORT = ROOT / "frontier/iterations/i165-square-expansion-multiplicity.md"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def canonical(obj):
    return (json.dumps(obj, indent=2, sort_keys=True) + "\n").encode()


def domain():
    paths = {REPORT}
    for folder in (HERE, SOURCE):
        for path in folder.rglob("*"):
            assert not path.is_symlink(), path
            if path.is_file():
                paths.add(path)
    return paths


def check_entries(entries):
    for entry in entries:
        path = ROOT / entry["path"]
        assert path.is_relative_to(ROOT) and not path.is_symlink()
        data = path.read_bytes()
        assert len(data) == entry["size"], entry["path"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], \
            entry["path"]


def audit(event, args):
    if event == "open":
        _, mode, flags = args
        assert not (mode and any(c in mode for c in "wax+")), "write denied"
        assert not flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT |
                            os.O_TRUNC | os.O_APPEND), "write flags denied"
    if event in {"os.remove", "os.rename", "os.rmdir", "os.mkdir",
                 "os.chmod", "os.chown", "os.truncate", "os.utime",
                 "os.link", "os.symlink", "os.system", "os.posix_spawn",
                 "os.fork", "os.forkpty"}:
        raise PermissionError(event)
    if event.startswith(("socket.", "subprocess.", "ctypes.")) or event in {
            "os.exec", "os.spawn"}:
        raise PermissionError(event)
    if event == "exec":
        filename = args[0].co_filename
        if filename.startswith(str(ROOT)):
            assert Path(filename).resolve() in ALLOWED, \
                "ancestor code denied"


def immutable(mode):
    inventory_path = HERE / "owned-files.json"
    inventory = load(inventory_path)
    assert inventory["schema"] == "i166-owned-v1"
    manifest_paths = {ROOT / e["path"] for e in inventory["files"]}
    assert len(manifest_paths) == len(inventory["files"])
    skip = {HERE / "owned-files.json", HERE / "seal.json"}
    if mode == "--prevalidate":
        assert not (HERE / "seal.json").exists(), \
            "do not prevalidate over an existing seal"
        skip.add(HERE / "prevalidation.json")
    else:
        seal = load(HERE / "seal.json")
        assert seal["inventory_sha256"] == digest(inventory_path)
        assert seal["prevalidation_sha256"] == digest(
            HERE / "prevalidation.json")
        receipt = load(HERE / "prevalidation.json")
        assert receipt["status"] == "PASS"
        assert receipt["mode"] == "--prevalidate"
        initial = dict(inventory)
        initial["files"] = [
            e for e in inventory["files"]
            if e["path"] != str((HERE / "prevalidation.json")
                                .relative_to(ROOT))]
        assert hashlib.sha256(canonical(initial)).hexdigest() == \
            receipt["input_inventory_sha256"]
    assert domain() - skip == manifest_paths, "owned inventory is not exact"
    check_entries(inventory["files"])
    # This binds all external payload bytes, but executes none of their code.
    bindings = load(SOURCE / "external-bindings.json")
    check_entries(bindings["files"])
    tree = {x["path"]: x
            for x in load(ROOT / "sources/preprints-tree.json")["tree"]}
    for source in bindings["stipulated_blobs"]:
        data = (ROOT / source["local"]).read_bytes()
        blob = hashlib.sha1(
            b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert blob == source["git_sha"] == tree[source["path"]]["sha"]
    return inventory


def module(name):
    path = HERE / (name + ".py")
    assert path in ALLOWED
    return runpy.run_path(str(path))


def norm(obj):
    """JSON round-trip normalization (tuples -> lists) for comparison
    against payload bytes."""
    return json.loads(json.dumps(obj))


def replay():
    results = {}
    results["selftest"] = module("selftest166")["run"]()
    audit_report = module("audit_i165")["run"]()
    assert norm(audit_report) == load(HERE / "audit-01.json")
    results["audit_verdict"] = audit_report["verdict"]
    meta, graphs = module("bracegen")["run"]()
    assert norm(meta) == load(HERE / "bracegen-meta.json")
    assert norm(graphs) == load(HERE / "bracegen-graphs.json")
    results["census"] = module("census_check")["run"]()["status"]
    assert norm(module("bracediag")["run"]()) == load(HERE / "diag-01.json")
    assert norm(module("walk2")["run"]()) == load(HERE / "diag-02.json")
    assert norm(module("as_check")["run"]()) == load(
        HERE / "as-check-01.json")
    assert norm(module("survival")["run"]()) == load(
        HERE / "survival-01.json")
    assert norm(module("c4reduce")["run"]()) == load(
        HERE / "c4reduce-01.json")
    d1 = load(HERE / "diag-01.json")["summary"]
    d2 = load(HERE / "diag-02.json")["summary"]
    assert not d1["members_d_not_full"] and not d2["d_not_full"]
    assert not d1["all_members_q164_violations"]
    assert not d2["q164_violations"]
    results["graphs_diagnosed"] = (d1["enumerations_exhausted"] +
                                   d2["enumerations_exhausted"])
    results["as_splices"] = load(HERE / "as-check-01.json"
                                 )["summary"]["splices_checked"]
    results["survival_steps"] = load(HERE / "survival-01.json"
                                     )["summary"]["steps_checked"]
    results["limit"] = ("Exact evidence on enumerated finite samples; "
                        "the universal brace statement is not proved")
    return results


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode, "use -I -B"
    assert len(sys.argv) == 2 and sys.argv[1] in ("--prevalidate",
                                                  "--replay")
    mode = sys.argv[1]
    sys.addaudithook(audit)
    inventory = immutable(mode)  # byte checks precede owned diagnostics
    result = {"status": "PASS", "mode": mode, "results": replay(),
              "owned_payloads": len(inventory["files"]),
              "input_inventory_sha256": digest(HERE / "owned-files.json"),
              "report_sha256": digest(REPORT),
              "verifier_sha256": digest(Path(__file__)),
              "security": ("Read-only audit hook; no ancestor execution, "
                           "subprocess or network")}
    if mode == "--replay":
        result["seal_sha256"] = digest(HERE / "seal.json")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
