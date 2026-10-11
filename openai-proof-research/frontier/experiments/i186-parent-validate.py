"""Authenticate I186 and check formal incidences, not graph realizability."""
import collections
import itertools
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i185-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
OUTPUTS = {
    "frontier/iterations/i186-theta-region-balance.md":
        "28cc7156e7a069e6e821b21d190fb4e0e188b4b6e45dd22a62fc1255f5320bc8",
    "frontier/experiments/i186_theta_region_balance/analytic-attempt.md":
        "bc757e5332bccdebb16368890a6939fdf8e180f265ac09ca542e53520dc7cf53",
    "frontier/experiments/i186_theta_region_balance/reading-and-failures.md":
        "1f74a79202454d2cd6a2bb759d7b517bb7216fcc56af3093f297a8bfede0c2d3",
    "frontier/experiments/i186_theta_region_balance/input-authentication.json":
        "15e1c00e28da7279c4d0921a64c64af64e551dee256d1c0b44e7c8a479902cc0",
    "frontier/sources/i186_theta_region_balance/literature.md":
        "6e5fbcfbb2fadb978b2165acea00bcdca36cb0449e361c1b5795538b25e1cd3a",
}


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i186-theta-region-balance.md"}
    for directory in ("frontier/experiments/i186_theta_region_balance",
                      "frontier/sources/i186_theta_region_balance"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i186_theta_region_balance/input-authentication.json").read_bytes())
    assert len(receipt["inputs"]) == len(receipt["additional_source_receipts"]) == 7
    for row in receipt["inputs"] + receipt["additional_source_receipts"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == PREVIOUS["OUTPUTS"][row["path"]]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "inputs": receipt["inputs"],
            "additional_sources": receipt["additional_source_receipts"],
            "previous_proof_records": "unchanged"}


def components(edges):
    # Edge identities remain list positions, including parallel pairing edges.
    adjacency = collections.defaultdict(list)
    for i, (u, v) in enumerate(edges):
        adjacency[u].append((v, i))
        adjacency[v].append((u, i))
    unseen = set(adjacency)
    result = []
    while unseen:
        todo = [next(iter(unseen))]
        visited = set()
        while todo:
            v = todo.pop()
            if v not in visited:
                visited.add(v)
                todo.extend(w for w, _ in adjacency[v] if w not in visited)
        unseen -= visited
        result.append(visited)
    return adjacency, result


def circuit_count(edges):
    adjacency, groups = components(edges)
    assert all(len(neighbors) == 2 for neighbors in adjacency.values())
    return len(groups)


def path_pairs(edges):
    adjacency, groups = components(edges)
    pairs = set()
    for group in groups:
        ends = {v for v in group if len(adjacency[v]) == 1}
        assert len(ends) == 2
        assert all(len(adjacency[v]) in (1, 2) for v in group)
        pairs.add(frozenset(ends))
    return pairs


def noncrossing(order, pairs):
    positions = {v: i for i, v in enumerate(order)}
    intervals = [sorted((positions[u], positions[v])) for u, v in pairs]
    for (a, b), (c, d) in itertools.combinations(intervals, 2):
        assert not (a < c < b < d or c < a < d < b)


def formal_checks():
    # Exact coefficient identity in nB,nW,m,dB,dW,tB,tW.
    black_degree = (3, 0, -1, -1, 0, 0, -1)
    white_degree = (0, 3, -1, 0, -1, -1, 0)
    balance = (1, -1, 0, 0, 0, 0, 0)
    difference = tuple(b-w-3*s for b, w, s in
                       zip(black_degree, white_degree, balance))
    assert difference == (0, 0, 0, -1, 1, 1, -1)
    colors = {v: int(v in "135tz") for v in "123456st wz".replace(" ", "")}
    RI, RQ, TI, TQ = ["16", "54"], ["12", "34"], ["65"], ["23"]
    S = {frozenset(p) for p in ["12", "36", "45"]}
    # The length-one edge in F-L directly forces pair 14.
    assert frozenset("14") not in S
    short_K, short_TJ = ["s2", "t5", "36"], ["1s", "t4"]
    assert path_pairs(short_K + short_TJ) == S
    assert [sum(colors[v] for v in pair) for pair in short_K] == [0, 2, 1]
    KJQ, KIJ = ["2s", "3t"], ["6w", "5z"]
    K, TJ, RJ = KJQ + KIJ, ["1s", "tw", "z4"], ["st", "wz"]
    for pairs in (KJQ, KIJ):
        assert sum(colors[v] for pair in pairs for v in pair) == 2
        assert [sum(colors[v] for v in pair) for pair in pairs] == [0, 2]
    noncrossing("1234zwts", KJQ)
    noncrossing("1654zwts", KIJ)
    H = K + RI + RJ + RQ
    assert circuit_count(H) == 1
    circuit = "12st345zw61"
    assert {frozenset(p) for p in H} == {
        frozenset(p) for p in zip(circuit, circuit[1:])}
    assert len(set(circuit[:-1])) == 10
    assert path_pairs(K + TJ) == S
    assert circuit_count(K + TI + TJ + RQ) == 2
    assert circuit_count(K + RI + TJ + TQ) == 2
    # Same-colored ends require even path length, with interior surplus +/-1.
    for length in range(2, 22, 2):
        for endpoint_color in (0, 1):
            interior = [(endpoint_color + i) % 2 for i in range(1, length)]
            assert interior.count(1) - interior.count(0) == 1-2*endpoint_color
    return {
        "residual_balance_coefficient_identity": list(difference),
        "short_J_forced_pairings_and_color_counts": "PASS",
        "length_five_regions_balanced_and_noncrossing": True,
        "Hamiltonian_incidence_circuits": 1,
        "old_and_new_complement_circuits": [2, 2],
        "retained_pairs": ["12", "36", "45"],
        "scope": "Formal incidences and degree equations only; no graph realization or universal proof",
    }


def replay():
    before = authenticate()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before, "formal_checks": checks,
            "sealed_reference_replay": reference, "I186_computational_seal": False,
            "local_ear_mechanism": "PARKED", "Z184": "UNRESOLVED",
            "E183": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i186-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I186 hashes, symbolic checks and inherited 23-stage replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
