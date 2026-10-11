"""Finite formal incidence truth table, not a new graph experiment.

Load with exact.py. This checks the small attachment argument; it does
not decide which identifications arise in an actual H180 graph.
"""


def incidence_tests():
    local = [(0, 1), (2, 3)]
    pairings = [
        [(0, 1), (2, 3)],
        [(0, 2), (1, 3)],
        [(0, 3), (1, 2)],
    ]
    rows = []
    for identify_ac, identify_bd in product((False, True), repeat=2):
        forced = []
        if identify_ac:
            forced.append((0, 2))
        if identify_bd:
            forced.append((1, 3))
        for pairing in pairings:
            admissible = all(p in pairing for p in forced)
            if not admissible:
                continue
            # At this level each pair represents one interval. Repeated
            # incidences are length-zero intervals, never discarded.
            group, adj = components(range(4), pairing + local)
            assert all(len(adj[v]) == 2 for v in range(4))
            cross = pairing != local
            assert (len(group) == 1) == cross
            if forced:
                assert cross
            # Independent edge-walk test retaining individual edge IDs.
            unused = set(range(4))
            traversals = 0
            while unused:
                traversals += 1
                first = min(unused)
                start, at = (pairing + local)[first]
                unused.remove(first)
                while at != start:
                    options = [(w, i) for w, i in adj[at] if i in unused]
                    assert len(options) == 1
                    at, i = options[0]
                    unused.remove(i)
            assert traversals == len(group)
            rows.append({"identify_ac": identify_ac, "identify_bd": identify_bd,
                         "R": pairing, "singleton_intervals": len(forced),
                         "attachment_components": len(group),
                         "cross": cross})
    assert len(rows) == 6
    # No graph is built here. In the double-repeat case the four stubs
    # are already used by two singletons, leaving any other degree-two
    # vertices in forbidden closed components.
    return {"status": "PASS", "formal_rows": rows,
            "scope": "stub attachment only, not H180 realizability",
            "both_repetitions": "excluded analytically by H0 and nonempty remainder"}
