"""Immutable-bytes-first, read-only I165 prevalidation and sealed replay."""
import hashlib
import json
import os
from pathlib import Path
import runpy
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i165_square_expansion_multiplicity"
REPORT = ROOT / "frontier/iterations/i165-square-expansion-multiplicity.md"
EXCLUSIONS = {"owned-files.json", "seal.json", "prevalidation.json"}
ALLOWED = {HERE / (name+".py") for name in
           ("verify", "graphs", "search", "targeted", "deficit", "decisive",
            "fallback", "amplification")}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def canonical(obj):
    return (json.dumps(obj, indent=2, sort_keys=True)+"\n").encode()


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
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], entry["path"]


def audit(event, args):
    if event == "open":
        _, mode, flags = args
        assert not (mode and any(c in mode for c in "wax+")), "write denied"
        assert not flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT |
                            os.O_TRUNC | os.O_APPEND), "write flags denied"
    if event in {"os.remove", "os.rename", "os.rmdir", "os.mkdir", "os.chmod",
                 "os.chown", "os.truncate", "os.utime", "os.link", "os.symlink",
                 "os.system", "os.posix_spawn", "os.fork", "os.forkpty"}:
        raise PermissionError(event)
    if event.startswith(("socket.", "subprocess.", "ctypes.")) or event in {
            "os.exec", "os.spawn"}:
        raise PermissionError(event)
    if event == "exec":
        filename = args[0].co_filename
        if filename.startswith(str(ROOT)):
            assert Path(filename).resolve() in ALLOWED, "ancestor code denied"


def immutable(mode):
    inventory_path = HERE / "owned-files.json"
    inventory = load(inventory_path)
    assert inventory["schema"] == "i165-owned-v1"
    manifest_paths = {ROOT / e["path"] for e in inventory["files"]}
    assert len(manifest_paths) == len(inventory["files"])
    skip = {HERE/"owned-files.json", HERE/"seal.json"}
    if mode == "--prevalidate":
        assert not (HERE/"seal.json").exists(), "do not prevalidate over an existing seal"
        skip.add(HERE/"prevalidation.json")
    else:
        seal = load(HERE/"seal.json")
        assert seal["inventory_sha256"] == digest(inventory_path)
        assert seal["prevalidation_sha256"] == digest(HERE/"prevalidation.json")
        receipt = load(HERE/"prevalidation.json")
        assert receipt["status"] == "PASS" and receipt["mode"] == "--prevalidate"
        initial = dict(inventory)
        initial["files"] = [e for e in inventory["files"]
                            if e["path"] != str((HERE/"prevalidation.json").relative_to(ROOT))]
        assert hashlib.sha256(canonical(initial)).hexdigest() == receipt["input_inventory_sha256"]
    assert domain()-skip == manifest_paths, "owned inventory is not exact"
    check_entries(inventory["files"])
    # This binds all old payload bytes, but executes none of their code.
    bindings = load(SOURCE/"external-bindings.json")
    check_entries(bindings["files"])
    old_report = ROOT / "frontier/iterations/i164-structural-graph-discovery.md"
    old_seal = ROOT / "frontier/experiments/i164_structural_graph_discovery/seal.json"
    assert digest(old_report) == "19142c6dd6ba3758006b6bd4390ce10408f3648e5f3d2ea72a07e22d01e565cd"
    assert digest(old_seal) == "dbf9aff37eb3fbd30270ea3de0992a02fe185e46ed8236ac2a0c45bc4f9fe14d"
    tree = {x["path"]: x for x in load(ROOT/"sources/preprints-tree.json")["tree"]}
    for source in bindings["stipulated_blobs"]:
        data = (ROOT/source["local"]).read_bytes()
        blob = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        assert blob == source["git_sha"] == tree[source["path"]]["sha"]
    return inventory


def module(name):
    path = HERE / (name+".py")
    assert path in ALLOWED
    return runpy.run_path(str(path))


def replay():
    first = module("search")["run"](12, 5)
    assert first == load(HERE/"search-01.json")
    second = module("targeted")["run"](18, 5)
    assert second == load(HERE/"targeted-01.json")
    assert module("deficit")["run"](second) == load(HERE/"deficits-01.json")
    decisive = module("decisive")["run"]()
    assert decisive == load(HERE/"decisive-03.json")
    earlier = dict(decisive)
    del earlier["arm_fibres"]
    assert earlier == load(HERE/"decisive-02.json")
    assert module("amplification")["run"]() == load(HERE/"amplification-01.json")
    fallback = module("fallback")["run"](decisive)
    assert fallback == load(HERE/"fallback-02.json")
    earlier_fallback = dict(fallback)
    del earlier_fallback["splice_piece_affine_ranks"]
    assert earlier_fallback == load(HERE/"fallback-01.json")
    failures = load(HERE/"failures.json")
    for failure in failures["historical_failures_preserved"]:
        assert (HERE/failure["output"]).stat().st_size == failure["output_bytes"] == 0
        assert failure["status"] == "INCOMPLETE, NOT PASS"
    return {"search_steps": len(first), "targeted_steps": len(second),
            "max_targeted_N00": max(r["N00"] for r in second),
            "decisive": {k: decisive[k] for k in
                         ("h", "h_prime", "N00", "Pux", "Pvy", "D11", "gain", "arm_fibres")},
            "short_side_checks": len(fallback["short_side_bijections"]),
            "affine_ranks": [r["rank"] for r in fallback["counterexample_affine_ranks"]],
            "preserved_incomplete_runs": 2,
            "limit": "Exact encoded examples and provenance, not a universal proof of Q164"}


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode, "use -I -B"
    assert len(sys.argv) == 2 and sys.argv[1] in ("--prevalidate", "--replay")
    mode = sys.argv[1]
    sys.addaudithook(audit)
    inventory = immutable(mode)  # Every byte check precedes owned diagnostic execution.
    result = {"status": "PASS", "mode": mode, "results": replay(),
              "owned_payloads": len(inventory["files"]),
              "input_inventory_sha256": digest(HERE/"owned-files.json"),
              "report_sha256": digest(REPORT), "verifier_sha256": digest(Path(__file__)),
              "security": "Read-only audit hook; no ancestor execution, subprocess or network"}
    if mode == "--replay":
        result["seal_sha256"] = digest(HERE/"seal.json")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
