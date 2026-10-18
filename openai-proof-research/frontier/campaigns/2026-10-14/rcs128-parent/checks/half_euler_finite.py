#!/usr/bin/env python3
"""Bounded brute-force diagnostic, not a proof of the half-Euler lemma.
Author: Myeongjin Kang. SPDX-License-Identifier: MIT
Root author-side check, independent of the candidate's proposed algorithm.
"""
from collections import Counter
from itertools import combinations_with_replacement
import json


def solve(orbits, root):
    """Try every unused orbit and both actual directed lifts."""
    full = (1 << len(orbits)) - 1
    failed = set()

    def dfs(v, used):
        if used == full:
            return () if v == root else None
        if (v, used) in failed:
            return None
        for i, pair in enumerate(orbits):
            if used >> i & 1:
                continue
            for a, b in pair:
                if a == v:
                    suffix = dfs(b, used | (1 << i))
                    if suffix is not None:
                        return ((i, a, b),) + suffix
        failed.add((v, used))
        return None

    return dfs(root, 0)


def admissible(orbits, tau, parity=True):
    indeg, outdeg = Counter(), Counter()
    adj = {}
    for pair in orbits:
        for a, b in pair:
            outdeg[a] += 1
            indeg[b] += 1
            adj.setdefault(a, set()).add(b)
            adj.setdefault(b, set()).add(a)
    if not adj or 0 not in adj or indeg != outdeg:
        return False
    if parity and any(tau[v] == v and outdeg[v] % 2 for v in adj):
        return False
    seen, todo = {0}, [0]
    while todo:
        for w in adj[todo.pop()]:
            if w not in seen:
                seen.add(w)
                todo.append(w)
    return seen == set(adj)


def main():
    rows = []
    parity_failure = None
    for tau, maximum in [((0, 2, 1), 6), ((0, 1, 3, 2), 5)]:
        edge_types = sorted({min((a, b), (tau[b], tau[a]))
                             for a in range(len(tau)) for b in range(len(tau))})
        tested = 0
        for n in range(1, maximum + 1):
            for types in combinations_with_replacement(edge_types, n):
                # Even if both endpoints coincide, the two lifts are DISTINCT
                # edge copies exchanged by tau, as the theorem requires.
                orbits = tuple(((a, b), (tau[b], tau[a])) for a, b in types)
                if admissible(orbits, tau):
                    witness = solve(orbits, 0)
                    assert witness is not None, (tau, orbits)
                    assert len(witness) == n and len({x[0] for x in witness}) == n
                    assert witness[0][1] == witness[-1][2] == 0
                    assert all(x[2] == y[1] for x, y in zip(witness, witness[1:]))
                    tested += 1
                elif parity_failure is None and admissible(orbits, tau, parity=False):
                    if solve(orbits, 0) is None:
                        parity_failure = {'tau': tau, 'orbits': orbits}
        rows.append({'tau': tau, 'max_edge_orbits': maximum, 'admissible_cases': tested})
    assert parity_failure is not None
    print(json.dumps({'status': 'PASS', 'cases': rows,
                      'removed_parity_counterexample': parity_failure,
                      'scope': 'Finite directed multigraph diagnostic only; no general proof or RC algorithm verification.'}, indent=2))


if __name__ == '__main__':
    main()
