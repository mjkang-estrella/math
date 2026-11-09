#!/usr/bin/env python3
"""Exact sweep of Conjecture 2.1 classes and multiplier isomorphisms (ebc-review-r1).

Own code; nothing from the discovery lane is imported.

For a circulant C_m(L) translation x -> x+t is an automorphism, so for the
edge e0 = {0, s}
    B'(e0) = sum_x sum_y f(x, y, e0) = sum_x sum_z f(0, z, e0 - x)
           = sum_{t in Z_m} delta_0({t, t+s}),
where delta_0(e) = sum_{z != 0} sigma_0z(e)/sigma_0z (exact Fractions, with
multiplicity when 2s = 0 mod m).  delta_0 is computed by the splitting
formula from the BFS tables of source 0 only, using d(a, b) = d(0, b-a) and
sigma_ab = sigma_{0, b-a} (translation invariance).  Every edge of C_m(L)
lies in the orbit of some {0, s}, s in L, so uniformity <=> the |L| values
B'({0, s}) coincide.

Also: for each class pair (4,7), (4,8), (7,8) and each n it finds every
unit k mod m with k*(+-L_a) = +-L_b (a multiplier isomorphism), and checks
whether the connection sets are genuinely distinct (not the same graph).

Usage: sweep.py OUT.json NMIN NMAX
"""
import json
import sys
from collections import deque
from fractions import Fraction
from math import gcd

CLASSES = {
    3: lambda n: (20 + 8 * (n - 1), (1, 2 * n + 2, 2 * n + 4)),
    4: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 2 * n + 7)),
    5: lambda n: (20 + 16 * (n - 1), (1, 4 * n, 8 * n + 1)),
    6: lambda n: (28 + 16 * (n - 1), (1, 4 * n + 4, 8 * n + 5)),
    7: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 5, 4 * n + 11)),
    8: lambda n: (32 + 8 * (n - 1), (1, 2 * n + 7, 4 * n + 11)),
    9: lambda n: (49 + 14 * (n - 1), (1, 2 * n + 6, 4 * n + 9)),
}


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
        return None, None
    diam = max(d)

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
    vals = {}
    for s in L:
        vals[s] = sum((delta(t, (t + s) % m) for t in range(m)), Fraction(0))
    wiener0 = sum(d)
    return vals, (diam, wiener0, len(S))


def fr(q):
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def main():
    out, nmin, nmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rows = []
    iso = []
    for n in range(nmin, nmax + 1):
        for cl, f in CLASSES.items():
            m, L = f(n)
            vals, info = edge_values(m, L)
            if vals is None:
                rows.append({"class": cl, "n": n, "m": m, "L": L, "connected": False})
                continue
            diam, w0, deg = info
            nedges = m * deg // 2
            tot = sum(v * (m if (2 * s) % m else m // 2) for s, v in vals.items())
            distinct = sorted(set(vals.values()))
            rows.append({"class": cl, "n": n, "m": m, "L": L, "degree": deg,
                         "edges": nedges, "diameter": diam,
                         "values": {str(s): fr(v) for s, v in vals.items()},
                         "uniform": len(distinct) == 1,
                         "wiener_check": tot == m * w0,
                         "spread": fr(distinct[-1] - distinct[0])})
        for a, b in ((4, 7), (4, 8), (7, 8)):
            ma, La = CLASSES[a](n)
            mb, Lb = CLASSES[b](n)
            assert ma == mb
            A, B = conn(ma, La), conn(mb, Lb)
            ks = [k for k in range(1, ma) if gcd(k, ma) == 1 and
                  frozenset((k * x) % ma for x in A) == B]
            iso.append({"n": n, "m": ma, "pair": [a, b], "same_connection_set": A == B,
                        "multipliers": ks})
        print(n, [(r["class"], r.get("uniform")) for r in rows[-7:]],
              [(i["pair"], i["multipliers"][:2]) for i in iso[-3:]], flush=True)
    summary = {}
    for cl in CLASSES:
        rs = [r for r in rows if r["class"] == cl]
        summary[str(cl)] = {
            "n_range": [nmin, nmax],
            "all_connected": all(r.get("connected", True) for r in rs),
            "all_degree_6": all(r.get("degree") == 6 for r in rs),
            "uniform_n": [r["n"] for r in rs if r.get("uniform")],
            "nonuniform_n": [r["n"] for r in rs if r.get("uniform") is False],
            "all_wiener_checks": all(r.get("wiener_check") for r in rs),
        }
    iso_summary = {f"{p[0]}-{p[1]}": all(i["multipliers"] for i in iso if i["pair"] == p)
                   for p in ([4, 7], [4, 8], [7, 8])}
    distinct_sets = all(not i["same_connection_set"] for i in iso)
    json.dump({"summary": summary, "iso_found_for_every_n": iso_summary,
               "connection_sets_pairwise_distinct": distinct_sets,
               "rows": rows, "iso": iso}, open(out, "w"), indent=1)
    print(json.dumps({"summary": summary, "iso_found_for_every_n": iso_summary,
                      "connection_sets_pairwise_distinct": distinct_sets}))


if __name__ == "__main__":
    main()
