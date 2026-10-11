"""I184 proof-record authentication and inherited sealed-reference replay.

The small finite checks below concern only the written degree equation
and labeled pairing example, not graphs or a universal proof search.
"""
import hashlib
import itertools
import json
import re
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
OUTPUTS = {
    "frontier/iterations/i184-alternating-cycle.md":
        "4d2ad390caaf9d40ccdc3a78caf15a12eddeb043f44952b6eaf712f5794066ca",
    "frontier/experiments/i184_alternating_cycle/analytic-attempt.md":
        "7db93dbcbe08ef158dae0502fdf4261539e03d967a9bdb4fc4a03c950be7fd52",
    "frontier/experiments/i184_alternating_cycle/reading-and-failures.md":
        "47cae7389ff0e083df4128bd978847551a731c4b26ebd4077af099e28e6d453f",
    "frontier/experiments/i184_alternating_cycle/input-authentication.json":
        "d6718b21ad9e24f86e3de2120578b044cf5e0cc8aa1660e8f05e5488077cbe3c",
    "frontier/sources/i184_alternating_cycle/literature.md":
        "c4978526287a4d869e4bf8ab1fd375290315d39786e2b35690f83504bd5c3fe6",
}
PARENT = runpy.run_path(str(EXP / "i183-final-parent-validate.py"))


def sha(name):
    p = Path(name)
    assert not p.is_absolute() and ".." not in p.parts
    full = ROOT / p
    assert not full.is_symlink() and full.resolve().is_relative_to(ROOT)
    return hashlib.sha256(full.read_bytes()).hexdigest()


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i184-alternating-cycle.md"}
    for directory in ("frontier/experiments/i184_alternating_cycle",
                      "frontier/sources/i184_alternating_cycle"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i184_alternating_cycle/input-authentication.json").read_bytes())
    assert len(receipt["inputs"]) == 5
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"]
        if row["expected_sha256"] is not None:
            assert row["sha256"] == row["expected_sha256"]
            assert PARENT["ANCHORS"][row["path"]] == row["sha256"]
    literature = (ROOT / "frontier/sources/i184_alternating_cycle/literature.md").read_text()
    additional = re.findall(r"^([0-9a-f]{64})  (\S+)$", literature, flags=re.M)
    assert len(additional) == 7
    for digest, name in additional:
        assert sha(name) == digest
    assert sha("frontier/sources/i164_structural_graph_discovery/upstream-paper.tex") == \
        "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "additional_source_hashes_checked": 8}


def formal_checks():
    # h=r-s-2, with r,s in {0,1,2} and h nonnegative.
    solutions = [(r, s, r-s-2) for r, s in itertools.product(range(3), repeat=2)
                 if r-s-2 >= 0]
    assert solutions == [(2, 0, 0)]
    def components(edges):
        classes = [{i} for i in (1, 2, 3, 4)]
        for a, b in edges:
            merged = set().union(*(c for c in classes if a in c or b in c))
            classes = [c for c in classes if a not in c and b not in c] + [merged]
        return len(classes)
    R, S, T = [(1, 2), (3, 4)], [(2, 3), (4, 1)], [(2, 3), (4, 1)]
    assert components(R+T) == 1 and components(S+T) == 2
    return {"deficit_solutions": solutions, "removed_plus_added_components": 1,
            "retained_plus_added_components": 2,
            "scope": "Formal equation/pairing checks only, no graph realizability claim"}


def replay():
    before = authenticate()
    result, proc = PARENT["replay"]()
    assert result["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "formal_checks": formal_checks(), "sealed_reference_replay": result,
            "I184_computational_seal": False, "Z184": "UNRESOLVED",
            "E183": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i184-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: five I184 output hashes, input/source hashes and formal checks; "
          "inherited 23-stage replay", result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
