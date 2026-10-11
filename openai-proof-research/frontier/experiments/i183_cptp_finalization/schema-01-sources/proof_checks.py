# Adapted from authenticated same-I183 resumed/proof_checks.py; finalization scope.
"""Bookkeeping for the written shore proof; no completed graph is tested."""
from itertools import combinations, product


def proof_checks():
    boundary = ("x", "a", "b", "y", "d", "c")
    patch = {frozenset((a, b)) for a, b in
             zip(boundary, boundary[1:] + boundary[:1])}
    patch.add(frozenset(("x", "y")))
    black, white = {"x", "b", "d"}, {"a", "y", "c"}
    assert all(len(e & black) == len(e & white) == 1 for e in patch)
    possible_extra = [
        tuple(sorted((a, b))) for a, b in combinations(boundary, 2)
        if frozenset((a, b)) not in patch
        and (a in black) != (b in black)
        and a not in ("x", "y") and b not in ("x", "y")]
    assert sorted(possible_extra) == [("a", "d"), ("b", "c")]
    rows = []
    for repeated, majority, minority, outgoing in (
            (("a", "c"), black | {"t"}, white, {"b", "d", "t"}),
            (("b", "d"), white | {"t"}, black, {"a", "c", "t"})):
        shore_edges = patch | {frozenset((v, "t")) for v in repeated}
        degree = {v: sum(v in e for e in shore_edges)
                  for v in majority | minority}
        assert len(majority) == 4 and len(minority) == 3
        assert all(degree[v] == 3 for v in minority)
        assert {v for v in majority if degree[v] == 2} == outgoing
        assert all(degree[v] == 3 for v in majority - outgoing)
        assert all(len(e & majority) == len(e & minority) == 1 for e in shore_edges)
        # No graph or matching population is enumerated. This is the
        # balance equation internal=3, internal+crossing=4.
        crossing = len(majority) - len(minority)
        assert crossing == 1
        assert len(majority) - 2 < len(minority)
        rows.append({"repeated": repeated, "shore_vertices": 7,
                     "internal_edges": len(shore_edges),
                     "outgoing_vertices": sorted(outgoing),
                     "forced_matching_crossings": crossing})
    # All equality patterns of three outgoing endpoints, without graph
    # completion. Canonical restricted-growth words give five partitions.
    partitions = [word for word in product(range(3), repeat=3)
                  if word[0] == 0 and all(
                      word[i] <= 1 + max(word[:i]) for i in (1, 2))]
    assert len(partitions) == 5
    for word in partitions:
        disjoint_pairs = [(i, j) for i, j in combinations(range(3), 2)
                          if word[i] != word[j]]
        assert bool(disjoint_pairs) == (len(set(word)) > 1)
        if not disjoint_pairs:
            assert len(set(word)) == 1
            assert 7 + 1 < 13 + 6  # closed component too small for G
    return {"status": "PASS", "shore_cases": rows,
            "outside_endpoint_partitions": len(partitions),
            "scope": "formal cut and color bookkeeping, no new graph tests"}
