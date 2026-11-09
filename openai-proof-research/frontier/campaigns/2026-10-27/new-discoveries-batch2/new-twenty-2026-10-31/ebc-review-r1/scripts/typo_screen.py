#!/usr/bin/env python3
"""Typo-sensitivity screen (ebc-review-r1): which 3-circulants C_m(1, a, b),
1 < a < b <= m/2, connected and 6-regular, are edge-betweenness-uniform?

If some near variant of Class 4 at m = 32 (or 40) is uniform, the printed
Class 4 could be a misprint; this tests that.  Same exact single-source
method as sweep.py (code duplicated, not imported).  It also lists, for each
uniform graph, whether its connection set is a multiplier image of
{+-1, +-a, +-b} of another uniform one (multiplier classes), and whether the
graph is a multiplier image of Class 4 / 3 / 5 / 6 members of the same order.

Usage: typo_screen.py OUT.json m [m ...]
"""
import json
import sys
from collections import deque
from fractions import Fraction
from math import gcd


def conn(m, L):
    return frozenset(x % m for s in L for x in (s, -s)) - {0}


def bfs0(m, S):
    d = [-1] * m
    c = [0] * m
    d[0] = 0
    c[0] = 1
    q = deque([0])
    while q:
        u = q.popleft()
        for g in S:
            v = (u + g) % m
            if d[v] < 0:
                d[v] = d[u] + 1
                q.append(v)
            if d[v] == d[u] + 1:
                c[v] += c[u]
    return d, c


def edge_values(m, L):
    S = sorted(conn(m, L))
    d, c = bfs0(m, S)
    if min(d) < 0:
        return None

    def delta(a, b):
        tot = Fraction(0)
        for z in range(1, m):
            dz = d[z]
            k = 0
            if d[a] + 1 + d[(z - b) % m] == dz:
                k += c[a] * c[(z - b) % m]
            if d[b] + 1 + d[(z - a) % m] == dz:
                k += c[b] * c[(z - a) % m]
            if k:
                tot += Fraction(k, c[z])
        return tot
    return {s: sum((delta(t, (t + s) % m) for t in range(m)), Fraction(0)) for s in L}


def fr(q):
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def main():
    out = sys.argv[1]
    res = {}
    for m in map(int, sys.argv[2:]):
        uni = []
        tested = 0
        for a in range(2, m // 2 + 1):
            for b in range(a + 1, m // 2 + 1):
                L = (1, a, b)
                if len(conn(m, L)) != 6:
                    continue
                v = edge_values(m, L)
                if v is None:
                    continue
                tested += 1
                if len(set(v.values())) == 1:
                    uni.append([a, b, fr(next(iter(v.values())))])
        # multiplier classes among uniform graphs
        classes = []
        seen = set()
        units = [k for k in range(1, m) if gcd(k, m) == 1]
        for a, b, val in uni:
            if (a, b) in seen:
                continue
            A = conn(m, (1, a, b))
            orbit = []
            for a2, b2, _ in uni:
                B = conn(m, (1, a2, b2))
                if any(frozenset((k * x) % m for x in A) == B for k in units):
                    orbit.append([a2, b2])
                    seen.add((a2, b2))
            classes.append({"rep": [1, a, b], "value": val, "multiplier_orbit": orbit})
        res[str(m)] = {"tested_connected_6_regular": tested,
                       "uniform": uni, "uniform_multiplier_classes": classes}
        print(m, "tested", tested, "uniform", uni, flush=True)
    json.dump(res, open(out, "w"), indent=1)


if __name__ == "__main__":
    main()
