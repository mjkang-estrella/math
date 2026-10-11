"""Direct parent checks of Q173 certificates, without importing child programs."""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i173_brace_high_loss_octagons"
PRIME = 1009
assert all(PRIME % d for d in range(2, 32))


def connected(vertices, edges):
    vertices = set(vertices)
    if not vertices:
        return True
    adjacent = {v: set() for v in vertices}
    for u, v in edges:
        if u in vertices and v in vertices:
            adjacent[u].add(v)
            adjacent[v].add(u)
    seen = {next(iter(vertices))}
    todo = list(seen)
    while todo:
        for v in adjacent[todo.pop()] - seen:
            seen.add(v)
            todo.append(v)
    return seen == vertices


def rank_lower_bound(rows):
    """Full row rank modulo a prime certifies rational independence of integers."""
    matrix = [[x % PRIME for x in row] for row in rows]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = pow(matrix[rank][col], -1, PRIME)
        matrix[rank] = [x * scale % PRIME for x in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            scale = matrix[i][col]
            matrix[i] = [(x - scale * y) % PRIME for x, y in zip(matrix[i], matrix[rank])]
        rank += 1
        if rank == len(matrix):
            break
    return rank


def main():
    population = json.loads((BASE / "surgeries-attempt-01.json").read_bytes())
    certificates = json.loads((BASE / "post_analysis-attempt-01.json").read_bytes())
    assert population["tested"] == len(population["records"]) == len(certificates["records"]) == 236
    successes = Counter()
    failures = directions = empty_transports = 0
    rows = []
    for index, (a, cert) in enumerate(zip(population["records"], certificates["records"])):
        assert cert["record"] == index and cert["history"] == a["history"]
        g = a["graph"]
        edges = sorted(tuple(sorted(e)) for e in g["edges"])
        vertices = {v for e in edges for v in e}
        n = len(vertices)
        assert n == g["n"] and len(set(edges)) == len(edges) and all(u != v for u, v in edges)
        assert Counter(v for e in edges for v in e) == Counter({v: 3 for v in vertices})
        assert connected(vertices, edges)
        for removed in combinations(vertices, 2):
            assert connected(vertices - set(removed), edges)
        colour = {min(vertices): 0}
        pending = list(colour)
        while pending:
            u = pending.pop()
            for e in edges:
                if u not in e:
                    continue
                v = e[1] if e[0] == u else e[0]
                if v not in colour:
                    colour[v] = 1 - colour[u]
                    pending.append(v)
                assert colour[v] != colour[u]
        assert set(colour) == vertices
        darts = Counter()
        links = {v: {} for v in vertices}
        for face in g["faces"]:
            assert len(face) == len(set(face))
            for i, v in enumerate(face):
                w, u = face[(i + 1) % len(face)], face[i - 1]
                darts[v, w] += 1
                assert u not in links[v]
                links[v][u] = w
        assert darts == Counter([e for u, v in edges for e in ((u, v), (v, u))])
        assert n - len(edges) + len(g["faces"]) == 2
        for link in links.values():
            v = min(link)
            assert len({v, link[v], link[link[v]]}) == 3 and link[link[link[v]]] == v
        face_index, i, j = a["row"]["step"]
        face = g["faces"][face_index]
        assert len(face) == 8 and j - i == 4
        deletion_indices = [edges.index(tuple(sorted((face[k], face[(k + 1) % 8])))) for k in (i, j)]
        anchor = cert["anchor"]
        basis_cycles = cert["survivor_basis_cycles"]
        ambient = len(edges) - n + 1
        assert cert["survivor_rank"] == cert["ambient_degree_kernel_dimension"] == ambient
        for cycle in [anchor] + basis_cycles:
            assert len(cycle) == len(edges) and set(cycle) <= {0, 1}
            selected = [e for e, x in zip(edges, cycle) if x]
            assert Counter(v for e in selected for v in e) == Counter({v: 2 for v in vertices})
            assert connected(vertices, selected)
            assert any(cycle[k] for k in deletion_indices)
        basis = [[x - y for x, y in zip(c, anchor)] for c in basis_cycles]
        assert len(basis) == rank_lower_bound(basis) == ambient
        # This is a proved rational rank, not a modular estimate: it attains
        # the rational homogeneous degree-kernel upper bound.
        complete_pairs = [(z["N00"]["extensions"][0], z["Pux"]["extensions"][0])
                          for z in a["transport"]["records"]
                          if z["N00"]["extensions"] and z["Pux"]["extensions"]]
        empty_transports += int(not complete_pairs)
        for which, field in enumerate(("old_direction_coordinates", "path_direction_coordinates")):
            expected = [[x - y for x, y in zip(pair[which], complete_pairs[0][which])]
                        for pair in complete_pairs[1:]]
            assert [z["direction"] for z in cert[field]] == expected
            for z in cert[field]:
                coefficients = list(map(Fraction, z["coefficients"]))
                assert len(coefficients) == len(basis) and not any(map(Fraction, z["remainder"]))
                assert z["absorbed"]
                assert [sum(c * row[k] for c, row in zip(coefficients, basis))
                        for k in range(len(edges))] == z["direction"]
                directions += 1
        stage = len(a["history"])
        disjoint = {(i, j) for i, j in combinations(range(len(edges)), 2)
                    if not set(edges[i]) & set(edges[j])}
        extended = set()
        for i, j, matching in a["brace"]["extended_pairs"]:
            assert (i, j) in disjoint and (i, j) not in extended
            assert i in matching and j in matching and len(set(matching)) == len(matching)
            assert all(0 <= k < len(edges) for k in matching)
            assert Counter(v for k in matching for v in edges[k]) == Counter({v: 1 for v in vertices})
            extended.add((i, j))
        failed = {tuple(z) for z in a["brace"]["failed_pairs"]}
        assert disjoint == extended | failed and not extended & failed
        assert a["brace"]["brace"] == (stage == 2) == (not failed)
        if stage == 1:
            side = set(range(2 * a["m"] + 9, 2 * a["m"] + 16))
            cut = [k for k, e in enumerate(edges) if len(set(e) & side) == 1]
            assert len(cut) == 3 and failed == set(combinations(cut, 2))
            ports = [next(v for v in edges[k] if v in side) for k in cut]
            majority = colour[ports[0]]
            assert all(colour[v] == majority for v in ports)
            assert sum(1 if colour[v] == majority else -1 for v in side) == 1
            # Thus every perfect matching crosses this cut exactly once.
        successes[stage] += len(extended)
        failures += len(failed)
        assert all(a["row"][k] == 0 for k in ("ell", "t", "eta", "delta_V", "delta_R", "epsilon"))
        rows.append(dict(record=index, m=a["m"], stage=stage, n=n,
                         certified_rational_survivor_rank=ambient, brace=stage == 2))
    assert successes == {1: 26076, 2: 302844} and failures == 72
    assert directions == 1500 and empty_transports == 6
    assert sum(r["brace"] for r in rows) == 212
    result = dict(status="PASS", records=rows, direct_matching_witnesses=dict(successes),
                  structurally_impossible_pairs=failures, rational_absorption_identities=directions,
                  empty_canonical_transports=empty_transports,
                  method="Direct graph, cycle, matching and rational-coordinate checks; modular full-rank minor plus rational ambient upper bound. No child code imported.",
                  limits="Not an independent exhaustive cycle/path or three-cut enumeration; those are covered by sealed replay.")
    with (BASE.parent / "i173-parent-certificates.json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: 236 exact survivor-rank certificates, 328920 matchings, 72 tight-cut failures, 1500 rational identities")


if __name__ == "__main__":
    main()
