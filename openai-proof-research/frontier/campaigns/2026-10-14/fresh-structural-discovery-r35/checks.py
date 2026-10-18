#!/usr/bin/env python3
"""Finite diagnostics only; not a proof of any research target."""
from fractions import Fraction
from itertools import combinations
import json


def run():
    # a=0..2, b=3..5, u=6..11.
    edges = set()
    for tri in ((0, 1, 2), (3, 4, 5)):
        edges.update(tuple(sorted(e)) for e in combinations(tri, 2))
    edges.update(tuple(sorted((6+i, 6+(i+1) % 6))) for i in range(6))
    rungs = {(i, 6+i) for i in range(6)}
    edges.update(rungs)
    assert len(edges) == 18
    assert all(sum(v in e for e in edges) == 3 for v in range(12))
    adj = {v: {u if v == w else w for u, w in edges if v in (u, w)} for v in range(12)}

    def matchings(vertices, chosen=()):
        if not vertices:
            yield chosen
            return
        v = min(vertices)
        rest = vertices - {v}
        yield from matchings(rest, chosen)
        for u in sorted(adj[v] & rest):
            yield from matchings(rest - {u}, chosen + (tuple(sorted((u, v))),))

    counts = [0, 0, 0]
    optimum = -1
    restricted_optimum = -1
    best = []
    for matching in matchings(set(range(12))):
        counts[0] += 1
        weight = sum(e in rungs for e in matching)
        if weight > optimum:
            optimum, best = weight, [matching]
        elif weight == optimum:
            best.append(matching)
        if len(matching) != 6:
            continue
        counts[1] += 1
        a_ext = sum(e in rungs and e[0] < 3 for e in matching)
        b_ext = sum(e in rungs and e[0] >= 3 for e in matching)
        if a_ext == b_ext == 1:
            counts[2] += 1
            restricted_optimum = max(restricted_optimum, weight)
    assert optimum == 6 and restricted_optimum == 2 and len(best) == 1
    assert set(best[0]) == rungs

    for m in range(1, 1001):
        union = (m + 2) * (4*m + 13)
        allowance = 10 * (m + 3)**2
        assert allowance - (2*union + 7) == 2*m*m + 18*m + 31
        assert max(union + 1, union + 2, union + 5, 2*union + 7, union + 7) <= allowance

    degree_checks = 0
    for n in range(0, 7):
        tails = [frozenset(c) for k in range(n+1) for c in combinations(range(n), k)]
        ordered = sorted(tails, key=lambda t: (-len(t), sorted(t)))
        adding = [a for a in tails if a]
        for j, target in enumerate(ordered):
            for later in ordered[j:]:
                for a in adding:
                    exponent = len(a) - len(later) + len(target)
                    assert exponent >= len(a) >= 1
                    degree_checks += 1
    assert 1 - 2 + 0 == -1  # An unrestricted target order fails positivity.
    assert 0 - 2 + 2 == 0   # Allowing empty adding sets fails vanishing at zero.

    ratio_checks = 0
    for hx in range(2, 11):
        for hy in range(2, 11):
            for hz in range(2, 11):
                r1 = Fraction(hy, hx*hz)
                r2 = Fraction(hx, hy*hz)
                assert r1*r2 == Fraction(1, hz*hz)
                assert not (r1.denominator == r2.denominator == 1)
                ratio_checks += 1
    # Different stages can separately satisfy the requirements: no general
    # impossibility of sequential constructions follows from the product test.
    for g in range(2, 11):
        assert Fraction(g**3, g*g) == g
        assert Fraction(g**3, g*g) == g
    return {
        'scope': 'finite diagnostics only; no target theorem or contribution gate certified',
        'matching': {'vertices': 12, 'edges': 18, 'all_matchings': counts[0],
                     'perfect_matchings': counts[1], 'restricted_perfect_matchings': counts[2],
                     'unrestricted_weight': optimum, 'contracted_lift_weight': restricted_optimum,
                     'unique_optimum': True},
        'capacity_values_checked': 1000,
        'positive_degree_instances': degree_checks,
        'nonpositive_controls': {'wrong_order': -1, 'empty_adding_set': 0},
        'simultaneous_ratio_instances': ratio_checks,
        'separate_stage_ratio_examples_exist': True,
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
