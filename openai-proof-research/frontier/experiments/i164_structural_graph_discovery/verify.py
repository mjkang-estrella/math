"""Read-only I164 prevalidation/replay. Invoke python -I -B verify.py MODE."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i164_structural_graph_discovery"
REPORT = ROOT / "frontier/iterations/i164-structural-graph-discovery.md"
INVENTORY = HERE / "owned-files.json"
SEAL = HERE / "seal.json"


def deny_side_effects(event, args):
    if event == "open":
        mode, flags = args[1], args[2]
        if (isinstance(mode, str) and any(c in mode for c in "wax+")) or (
                isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR |
                                                   os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise RuntimeError("read-only replay denied file write")
    if event.startswith(("socket.", "subprocess.", "os.exec", "os.spawn")) or event in {
            "os.system", "os.fork", "os.posix_spawn", "os.remove", "os.rmdir",
            "os.rename", "os.mkdir", "os.link", "os.symlink", "os.chmod", "os.truncate"}:
        raise RuntimeError("read-only replay denied side effect: " + event)


sys.addaudithook(deny_side_effects)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def owned_paths():
    found = [REPORT]
    for directory in (HERE, SOURCE):
        for p in directory.rglob("*"):
            assert not p.is_symlink(), "owned symlinks are not permitted"
            if p.is_file() and p not in (INVENTORY, SEAL):
                found.append(p)
    return sorted(found, key=lambda p: p.relative_to(ROOT).as_posix())


def load(name):
    path = HERE / (name + ".py")
    assert path.parent == HERE and path.is_file()
    spec = importlib.util.spec_from_file_location("owned_i164_" + name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def printed_json(module):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        module.main()
    return json.loads(buf.getvalue())


def source_checks():
    contracts = read_json(SOURCE / "contracts.json")
    assert contracts["commit"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
    tree_path = ROOT / "sources/preprints-tree.json"
    assert digest(tree_path) == contracts["tree_sha256"]
    tree = {x["path"]: x for x in read_json(tree_path)["tree"]}
    for item in contracts["sources"]:
        p = ROOT / item["local"]
        assert p.parent == SOURCE
        data = p.read_bytes()
        assert digest(p) == item["sha256"]
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        assert blob == item["git_sha"] == tree[item["path"]]["sha"]
        assert (ROOT / item["reused_from"]).read_bytes() == data
        assert item["url"].endswith(contracts["commit"] + "/" + item["path"])
    for item in read_json(SOURCE / "reading-ranges.json"):
        p = SOURCE / item["file"]
        assert p.parent == SOURCE
        assert digest(p) == item["sha256"]
        lines = p.read_bytes().splitlines(keepends=True)
        for region in item.get("ranges", []):
            data = b"".join(lines[region["first"]-1:region["last"]])
            assert hashlib.sha256(data).hexdigest() == region["sha256"]
    return len(contracts["sources"])


def expected_failure(name, expected_line):
    try:
        load(name).main()
    except AssertionError as exc:
        last = traceback.extract_tb(exc.__traceback__)[-1]
        assert Path(last.filename) == HERE / (name + ".py")
        assert last.lineno == expected_line
        return dict(module=name, status="EXPECTED_HISTORICAL_FAILURE", line=last.lineno)
    raise AssertionError("historical failure unexpectedly passed")


def main():
    assert sys.dont_write_bytecode
    assert sys.flags.isolated, "use -I"
    assert sys.argv[1:] in (["--prevalidate"], ["--replay"])
    mode = sys.argv[1]
    sources = source_checks()
    discovery = printed_json(load("explore"))
    assert discovery == read_json(HERE / "discovery-01.json")
    expansion = printed_json(load("expansion_probe"))
    assert expansion == read_json(HERE / "expansion-discovery-01.json")
    states = [load("state_probe").data(m) for m in range(4, 22, 2)]
    assert states == read_json(HERE / "state-discovery-01.json")
    d = load("diagnostics_v3")
    diagnostics = d.main()
    assert diagnostics == read_json(HERE / "diagnostics-03.json")
    base = load("explore")
    ranks = []
    for entry in discovery["results"]:
        g = entry["best"]
        if g is None:
            continue
        edges = [tuple(e) for e in g["edges"]]
        cycles = base.cycles(g["n"], edges)
        r = d.rank([[int(e in c)-int(e in cycles[0]) for e in edges] for c in cycles[1:]])
        assert r == g["n"] // 2 + 1
        ranks.append(dict(n=g["n"], h=len(cycles), affine_rank=r))
    failures = [expected_failure("diagnostics", 141),
                expected_failure("diagnostics_v2", 144)]
    summary = dict(status="PASS", mode=mode, stipulated_source_blobs=sources,
                   encoded_graphs=sum(x["checked"] for x in discovery["results"]),
                   square_expansions=expansion["tested"],
                   minimum_expansion_gain=expansion["minimum_gain"],
                   bipyramids=len(states), prism_orders=len(diagnostics["prisms"]),
                   directed_P4_checks=sum(x["directed_P4_checks"] for x in diagnostics["prisms"]),
                   boundary_identities=len(diagnostics["expansion_identity"]),
                   vandermonde_cases=diagnostics["vandermonde_cases"],
                   representative_ranks=ranks, historical_failures=failures,
                   limitations="finite and provenance checks only; Q164 remains unproved")
    if mode == "--replay":
        inventory = read_json(INVENTORY)
        seal = read_json(SEAL)
        assert seal["inventory_sha256"] == digest(INVENTORY)
        assert seal["inventory"] == INVENTORY.relative_to(ROOT).as_posix()
        assert seal["prevalidation_sha256"] == digest(HERE / "prevalidation.json")
        assert read_json(HERE / "prevalidation.json")["status"] == "PASS"
        entries = inventory["files"]
        actual = [p.relative_to(ROOT).as_posix() for p in owned_paths()]
        assert actual == [x["path"] for x in entries], "owned inventory domain mismatch"
        for item in entries:
            p = ROOT / item["path"]
            assert p.stat().st_size == item["size"]
            assert digest(p) == item["sha256"], "owned byte drift: " + item["path"]
        summary.update(owned_files=len(entries), inventory_sha256=digest(INVENTORY),
                       seal_sha256=digest(SEAL), report_sha256=digest(REPORT),
                       verifier_sha256=digest(Path(__file__)))
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
