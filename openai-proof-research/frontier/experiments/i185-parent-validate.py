"""Authenticate the I185 proof record and replay the existing sealed reference.

Formal checks concern only labeled pairings and path edge types, not
graph generation, admissible-instance tests or a universal theorem.
"""
import hashlib
import itertools
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i184-parent-validate.py"))
REFERENCE = PREVIOUS["PARENT"]
OUTPUTS = {
    "frontier/iterations/i185-connected-reconnection.md":
        "4021b5fb63fd9b4742dd7bcb9c35be2e33a492cac16d83654b3f8fb477310a9d",
    "frontier/experiments/i185_connected_reconnection/analytic-attempt.md":
        "b2050c06cdf79dd9e863844a5432fbc337faad2375a1a961e6c7c94c96aa5fac",
    "frontier/experiments/i185_connected_reconnection/reading-and-failures.md":
        "13066230f26c5f1d3b2385d17e5ae6c8b66ddc969ddcc713f7f98aca77557827",
    "frontier/experiments/i185_connected_reconnection/input-authentication.json":
        "f0151d4ccf4855576c9d3dd292328880f7150c1c951b10852189a630dd6f4e14",
    "frontier/sources/i185_connected_reconnection/literature.md":
        "cead5110dbb5003b34b5a86a5012154d17a5f01c042c10a383b9ef05ee20f7cf",
}


def sha(name):
    p = Path(name)
    assert not p.is_absolute() and ".." not in p.parts
    full = ROOT / p
    assert not full.is_symlink() and full.resolve().is_relative_to(ROOT)
    return hashlib.sha256(full.read_bytes()).hexdigest()


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i185-connected-reconnection.md"}
    for directory in ("frontier/experiments/i185_connected_reconnection",
                      "frontier/sources/i185_connected_reconnection"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i185_connected_reconnection/input-authentication.json").read_bytes())
    assert len(receipt["inputs"]) == 7 and len(receipt["additional_source_receipts"]) == 6
    for row in receipt["inputs"] + receipt["additional_source_receipts"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == PREVIOUS["OUTPUTS"][row["path"]]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "inputs": receipt["inputs"],
            "additional_sources": receipt["additional_source_receipts"],
            "previous_proof_record": "unchanged"}


def formal_checks():
    def count(edges):
        groups = [{v} for v in {v for e in edges for v in e}]
        for u, v in edges:
            joined = set().union(*(g for g in groups if u in g or v in g))
            groups = [g for g in groups if u not in g and v not in g] + [joined]
        return len(groups)
    L = [(1, 2), (3, 4), (5, 6)]
    N = [(2, 3), (4, 5), (6, 1)]
    S = [(1, 2), (3, 6), (4, 5)]
    assert count(L+N) == 1 and count(S+L) == count(S+N) == 2
    assert all((a-b) % 2 for a, b in L+N+S)
    for (a, b), (c, d) in itertools.combinations([tuple(sorted(e)) for e in S], 2):
        assert not (a < c < b < d or c < a < d < b)
    # I and Q both have nonmatching ends, while J has matching ends.
    # Exhaust a small formal length range to check the stated edge counts.
    checked = 0
    for r, s, t in itertools.product(range(4), repeat=3):
        I = [j % 2 for j in range(2*r+1)]
        J = [1-j % 2 for j in range(2*s+1)]
        Q = [j % 2 for j in range(2*t+1)]
        assert (I.count(0), I.count(1)) == (r+1, r)
        assert (J.count(0), J.count(1)) == (s, s+1)
        assert (Q.count(0), Q.count(1)) == (t+1, t)
        assert len(Q+J) - len(I+J) == 2*(t-r)
        assert I.count(1)+Q.count(0) == I.count(0)+Q.count(1) == r+t+1
        checked += 1
    return {"six_incidence_counts": {"L_union_N": 1, "S_union_L": 2, "S_union_N": 2},
            "bipartite_pair_types": True, "S_noncrossing": True,
            "formal_length_cases": checked, "excluded_simple_graph_case": "r=t=0",
            "scope": "Formal pairing and edge-type bookkeeping, not realizability or graph tests"}


def replay():
    before = authenticate()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "formal_checks": formal_checks(), "sealed_reference_replay": reference,
            "I185_computational_seal": False, "Z184": "UNRESOLVED",
            "E183": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i185-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I185 hashes, formal checks and inherited 23-stage replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
