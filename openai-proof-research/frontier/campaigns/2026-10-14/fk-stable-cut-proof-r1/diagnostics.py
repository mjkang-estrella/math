#!/usr/bin/env python3
"""Independent exact finite diagnostics; no infinite-limit certification.

Original code MIT. Enumerate valid offspring words, independently of the
candidate's recursive tree enumerator. Do not import or execute candidate code.
"""
from fractions import Fraction as Q
from itertools import product
import json


def walk_law(p, n):
    d = {0: Q(1)}
    for _ in range(n):
        e = {}
        for x, v in d.items():
            for k, pk in p.items():
                e[x+k-1] = e.get(x+k-1, Q(0)) + v*pk
        d = e
    return d


def decode(word):
    # Stack of open node slots records preorder depths and child indices.
    pending = [(None, 0)]
    depths, children = [], [[] for _ in word]
    for i, k in enumerate(word):
        if not pending:
            return None
        parent, depth = pending.pop()
        depths.append(depth)
        if parent is not None:
            children[parent].append(i)
        pending.extend((i, depth+1) for _ in range(k))
    if pending:
        return None
    ends = []
    for i in range(len(word)):
        slots = 1
        j = i
        while slots:
            slots += word[j]-1
            j += 1
        ends.append(j)
    return depths, children, ends


identity_cases = boundary_cases = valid_words = 0
max_descent = 0
for p in ({0: Q(9,16), 2: Q(3,8), 4: Q(1,16)},
          {0: Q(1,2), 1: Q(1,4), 3: Q(1,4)}):
    assert sum(p.values()) == sum(k*v for k, v in p.items()) == 1
    laws = [walk_law(p, n) for n in range(10)]
    pi = [Q(0)] + [laws[n].get(-1, Q(0))/n for n in range(1,10)]
    for n in range(1,10):
        ts = []
        for word in product(p, repeat=n):
            if sum(word) != n-1:
                continue
            decoded = decode(word)
            if decoded is None:
                continue
            depths, children, ends = decoded
            weight = Q(1)
            for k in word:
                weight *= p[k]
            ts.append((word, children, ends, weight))
            valid_words += 1
            h = depths + [0]
            max_descent = max(max_descent, *(h[j]-h[j+1] for j in range(n)))
            for i, cs in enumerate(children):
                if not cs:
                    continue  # A self/leaf term is omitted in the path integral.
                d, end = h[i], ends[i]
                # The component {H>d} containing any proper descendant starts
                # at i and ends in the interpolation cell [end-1,end].
                assert h[i+1] == d+1
                assert all(h[j] > d for j in range(i+1, end))
                assert h[end] <= d
                right = Q(end-1) + Q(h[end-1]-d, h[end-1]-h[end])
                assert Q(end-1) < right <= end
                # Compared with full subtree cells [i,end), only the last
                # endpoint cell differs. Proper descendants omit [i,i+1).
                boundary_cases += 1
        assert sum((t[3] for t in ts), Q(0)) == pi[n]
        if not pi[n]:
            continue
        for g in (lambda k: 1, lambda k: k, lambda k: k*(k>2)):
            for f in (lambda s: 1, lambda s: s*s, lambda s: s == 3):
                lhs = sum((w*sum(g(word[v])*sum(f(ends[c]-c) for c in cs)
                                 for v, cs in enumerate(children))
                           for word, children, ends, w in ts), Q(0))/pi[n]
                rhs = Q(n)/laws[n][-1]*sum(
                    (f(s)*pi[s]*sum((k*pk*g(k)*laws[n-1-s].get(1-k,Q(0))
                                      for k, pk in p.items()), Q(0))
                     for s in range(1,n)), Q(0))
                assert lhs == rhs, (p, n, lhs, rhs)
                identity_cases += 1

assert max_descent > 1  # Preorder descents, not merely contour +/-1 steps.
print(json.dumps({"status": "PASS_FINITE_DIAGNOSTICS_ONLY",
                  "valid_offspring_words": valid_words,
                  "selected_child_identity_cases": identity_cases,
                  "nonleaf_preorder_component_cases": boundary_cases,
                  "maximum_tested_preorder_descent": max_descent,
                  "includes_unary_law_to_test_zero_remainder": True,
                  "infinite_limits_proved_by_code": False}, indent=2)+"\n", end="")
