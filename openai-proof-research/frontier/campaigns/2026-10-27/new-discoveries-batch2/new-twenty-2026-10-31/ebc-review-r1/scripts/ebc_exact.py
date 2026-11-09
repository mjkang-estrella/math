#!/usr/bin/env python3
"""Independent exact edge-betweenness computation (ebc-review-r1).

Written from scratch for this review; imports nothing from the discovery lane.

Definition 1.1 of Newman-Miranda-Florez-Narayan (EJGTA 8(2) 2020):
    B'(e) = sum over ORDERED pairs (x, y) of distinct vertices of
            sigma_xy(e) / sigma_xy,
where sigma_xy is the number of shortest x-y paths and sigma_xy(e) the
number of them containing the edge e.  Pairs with x or y an endpoint of e
are included (the source's Lemma 1.1 lower bound 2 relies on this).

Circulant C_m(L) (source's definition): vertices Z_m, i ~ i+j and i ~ i-j
for every j in L.

Two methods, both over ALL edges and ALL ordered pairs, NO symmetry shortcut:
  M1  BFS distance/path-count tables from every vertex, then the splitting
      formula sigma_xy(uv) = s_xu s_vy [d_xu+1+d_vy = d_xy]
                            + s_xv s_uy [d_xv+1+d_uy = d_xy].
  M2  (only if --enumerate) literal enumeration of every shortest path of
      every ordered pair by depth-first search along the BFS layers, counting
      edge occurrences directly.  This uses no splitting formula.
Also reports a variant V that EXCLUDES pairs having x or y in e, and the
Wiener identity sum_e B'(e) = sum_{x != y} d(x, y).

Usage: ebc_exact.py OUT.json [--enumerate] m:s1,s2,... [m:s1,...] ...
"""
import json
import sys
from collections import deque
from fractions import Fraction


def circulant(m, steps):
    adj = [set() for _ in range(m)]
    for i in range(m):
        for j in steps:
            for k in ((i + j) % m, (i - j) % m):
                if k != i:
                    adj[i].add(k)
    return [sorted(a) for a in adj]


def bfs(adj, s):
    m = len(adj)
    d = [-1] * m
    c = [0] * m
    d[s] = 0
    c[s] = 1
    q = deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if d[v] < 0:
                d[v] = d[u] + 1
                q.append(v)
            if d[v] == d[u] + 1:
                c[v] += c[u]
    return d, c


def method1(adj, edges, D, S):
    m = len(adj)
    full = {}
    excl = {}
    for (u, v) in edges:
        tot = Fraction(0)
        tex = Fraction(0)
        for x in range(m):
            Dx, Sx = D[x], S[x]
            for y in range(m):
                if x == y:
                    continue
                dxy = Dx[y]
                k = 0
                if Dx[u] + 1 + D[v][y] == dxy:
                    k += Sx[u] * S[v][y]
                if Dx[v] + 1 + D[u][y] == dxy:
                    k += Sx[v] * S[u][y]
                if k:
                    f = Fraction(k, Sx[y])
                    tot += f
                    if x not in (u, v) and y not in (u, v):
                        tex += f
        full[(u, v)] = tot
        excl[(u, v)] = tex
    return full, excl


def method2(adj, D):
    """Literal enumeration of all shortest paths of all ordered pairs."""
    m = len(adj)
    cnt = {}
    npaths_check = {}
    for x in range(m):
        Dx = D[x]
        for y in range(m):
            if x == y:
                continue
            paths = []
            stack = [(x, [x])]
            while stack:
                w, p = stack.pop()
                if w == y:
                    paths.append(p)
                    continue
                for z in adj[w]:
                    # z must be one step further from x and on a geodesic to y
                    if Dx[z] == Dx[w] + 1 and D[z][y] == Dx[y] - Dx[z]:
                        stack.append((z, p + [z]))
            sig = len(paths)
            npaths_check[(x, y)] = sig
            per = {}
            for p in paths:
                for a, b in zip(p, p[1:]):
                    e = (min(a, b), max(a, b))
                    per[e] = per.get(e, 0) + 1
            for e, k in per.items():
                cnt[e] = cnt.get(e, Fraction(0)) + Fraction(k, sig)
    return cnt, npaths_check


def step_of(u, v, m):
    s = (v - u) % m
    return min(s, m - s)


def fr(q):
    return f"{q.numerator}/{q.denominator}" if q.denominator != 1 else str(q.numerator)


def analyse(m, steps, enumerate_paths):
    adj = circulant(m, steps)
    deg = sorted(set(len(a) for a in adj))
    edges = sorted({(min(u, v), max(u, v)) for u in range(m) for v in adj[u]})
    D, S = [], []
    for s in range(m):
        d, c = bfs(adj, s)
        D.append(d)
        S.append(c)
    connected = all(d >= 0 for d in D[0])
    res = {"m": m, "steps": steps, "degrees": deg, "edges": len(edges),
           "connected": connected}
    if not connected:
        return res
    res["diameter"] = max(D[0])
    res["bipartite_all_steps_odd_and_m_even"] = (m % 2 == 0 and all(s % 2 for s in steps))
    wiener_ordered = sum(D[x][y] for x in range(m) for y in range(m) if x != y)
    full, excl = method1(adj, edges, D, S)
    vals = sorted(set(full.values()))
    by_step = {}
    for e, val in full.items():
        by_step.setdefault(step_of(e[0], e[1], m), set()).add(val)
    exvals = sorted(set(excl.values()))
    res.update({
        "wiener_ordered": wiener_ordered,
        "sum_B_equals_wiener": sum(full.values()) == wiener_ordered,
        "M1_distinct_values": [fr(v) for v in vals],
        "M1_distinct_values_float": [float(v) for v in vals],
        "M1_uniform": len(vals) == 1,
        "M1_by_step": {str(k): [fr(v) for v in sorted(vs)] for k, vs in sorted(by_step.items())},
        "M1_edge_0_s": {str(s): fr(full[(min(0, s % m), max(0, s % m))]) for s in steps},
        "V_excluding_endpoint_pairs_distinct": [fr(v) for v in exvals],
        "V_uniform": len(exvals) == 1,
        "uniform_value_if_uniform_ordered": fr(Fraction(wiener_ordered, len(edges))),
        "sigma_from_0": {str(y): [D[0][y], S[0][y]] for y in range(m)},
    })
    if len(vals) > 1:
        res["max_minus_min"] = fr(vals[-1] - vals[0])
    if enumerate_paths:
        cnt, nchk = method2(adj, D)
        agree_sigma = all(nchk[(x, y)] == S[x][y] for (x, y) in nchk)
        agree = (set(cnt) == set(full)) and all(cnt[e] == full[e] for e in full)
        res["M2_sigma_agrees_with_BFS_counts"] = agree_sigma
        res["M2_agrees_with_M1_on_every_edge"] = agree
        res["M2_distinct_values"] = [fr(v) for v in sorted(set(cnt.values()))]
        res["M2_total_shortest_paths_ordered"] = sum(nchk.values())
    return res


def main():
    out = sys.argv[1]
    args = sys.argv[2:]
    enum = False
    if args and args[0] == "--enumerate":
        enum = True
        args = args[1:]
    results = []
    for a in args:
        ms, ss = a.split(":")
        m = int(ms)
        steps = [int(t) for t in ss.split(",")]
        r = analyse(m, steps, enum)
        results.append(r)
        brief = {k: r.get(k) for k in ("m", "steps", "degrees", "edges", "diameter",
                                        "M1_uniform", "M1_distinct_values",
                                        "M1_distinct_values_float", "M1_by_step",
                                        "max_minus_min", "sum_B_equals_wiener",
                                        "V_uniform", "M2_agrees_with_M1_on_every_edge",
                                        "M2_sigma_agrees_with_BFS_counts")}
        print(json.dumps(brief))
    with open(out, "w") as fh:
        json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
