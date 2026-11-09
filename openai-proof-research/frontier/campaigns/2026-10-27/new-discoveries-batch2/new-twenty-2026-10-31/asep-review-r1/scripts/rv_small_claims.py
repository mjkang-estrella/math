#!/usr/bin/env python3
"""Checks the source's qualitative neighbourhood statements at n = 4 and n = 5 (Sec. 5.2) with ordinary
polytope adjacency (exact rank 19 / 11). n = 4 vertices are obtained by closing Example 1 and the tours under S_4
(the source and [13] report 12 vertices = 2 orbits). usage: rv_small_claims.py N5.json OUT.json"""
import sys, json, itertools
from fractions import Fraction as F
sys.path.insert(0, __import__("os").path.dirname(__file__))
from rv_asep import rank, setup
def build(n, reps):
    arcs, idx, m, eqs, cuts, cutrows = setup(n)
    def act(p, x):
        y = [None] * m
        for k, (i, j) in enumerate(arcs): y[idx[(p[i], p[j])]] = x[k]
        return tuple(y)
    V = {}; 
    for r, x in enumerate(reps):
        for p in itertools.permutations(range(n)): V.setdefault(act(p, x), r)
    unit = lambda k: [1 if t == k else 0 for t in range(m)]
    def ts(x): return ({k for k in range(m) if x[k] == 0}, {s for s in range(len(cuts)) if sum(x[k] for k in range(m) if cutrows[s][k]) == 1})
    T = {x: ts(x) for x in V}
    def adj(x, y):
        return rank(eqs + [unit(k) for k in T[x][0] & T[y][0]] + [cutrows[s] for s in T[x][1] & T[y][1]], m) == m - 1
    return V, adj, m
out = {}
# n = 4
x4 = [F(1, 2) if v else F(0) for v in [1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1]]  # arcs order (0,1),(0,2),(0,3),(1,0),...
arcs4 = setup(4)[0]; X = [[0,1,0,1],[1,0,1,0],[1,0,0,1],[0,1,1,0]]
x4 = tuple(F(X[i][j], 2) for (i, j) in arcs4)
t4 = tuple(F(1) if j == (i + 1) % 4 else F(0) for (i, j) in arcs4)
V, adj, m = build(4, [x4, t4])
tours = [v for v in V if V[v] == 1]; fr = [v for v in V if V[v] == 0]
out["n4"] = {"num_vertices": len(V), "tour_degrees": sorted(sum(adj(t, w) for w in V if w != t) for t in tours),
             "fractional_adjacent_tour_counts": sorted(sum(adj(f, t) for t in tours) for f in fr),
             "claim_each_tour_adjacent_to_all_but_one": all(sum(adj(t, w) for w in V if w != t) == len(V) - 2 for t in tours)}
# n = 5
d = json.load(open(sys.argv[1])); reps = [tuple(F(s) for s in o["rep"]) for o in d["orbits"]]
V, adj, m = build(5, reps)
cls = {}
for r, x in enumerate(reps):
    nb = [V[y] for y in V if y != x and adj(x, y)]
    cls[r] = {"values": d["orbits"][r]["values"], "orbit_size": d["orbits"][r]["orbit_size"],
              "neighbours_per_orbit": {str(k): nb.count(k) for k in range(len(reps))}}
out["n5"] = {"num_vertices": len(V), "per_orbit": cls,
             "claim_every_vertex_has_neighbour_in_every_orbit": all(all(v > 0 for v in c["neighbours_per_orbit"].values()) for c in cls.values())}
json.dump(out, open(sys.argv[2], "w"), indent=1); print(json.dumps(out, indent=1))
