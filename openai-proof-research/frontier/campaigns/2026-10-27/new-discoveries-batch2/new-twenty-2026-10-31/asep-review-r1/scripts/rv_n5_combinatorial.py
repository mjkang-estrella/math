#!/usr/bin/env python3
"""Rank-free cross-check of the n = 5 neighbourhood sizes (reviewer's own).
Given the complete vertex list V of P_ASEP^5 (from rv_n5_table2.py output, re-certified here), x and y are
adjacent iff the only vertices of V tight on every constraint tight at both x and y are x and y themselves
(the minimal face of the midpoint is the convex hull of the vertices it contains).
usage: rv_n5_combinatorial.py IN.json OUT.json"""
import sys, json, itertools
from fractions import Fraction as F
sys.path.insert(0, __import__("os").path.dirname(__file__))
from rv_asep import setup
n = 5; arcs, idx, m, eqs, cuts, cutrows = setup(n)
d = json.load(open(sys.argv[1]))
def act(p, x):
    y = [None] * m
    for k, (i, j) in enumerate(arcs): y[idx[(p[i], p[j])]] = x[k]
    return tuple(y)
V = set()
for o in d["orbits"]:
    x = tuple(F(s) for s in o["rep"])
    for p in itertools.permutations(range(n)): V.add(act(p, x))
V = sorted(V)
def tset(x):
    z = frozenset(k for k in range(m) if x[k] == 0)
    c = frozenset(s for s in range(len(cuts)) if sum(x[k] for k in range(m) if cutrows[s][k]) == 1)
    return z, c
TS = {x: tset(x) for x in V}
out = {"num_vertices": len(V), "orbits": []}
for o in d["orbits"]:
    x = tuple(F(s) for s in o["rep"]); zx, cx = TS[x]; nadj = 0
    for y in V:
        if y == x: continue
        zy, cy = TS[y]; Z = zx & zy; C = cx & cy
        inface = sum(1 for w in V if Z <= TS[w][0] and C <= TS[w][1])
        if inface == 2: nadj += 1
    out["orbits"].append({"orbit_size": o["orbit_size"], "values": o["values"], "rank_count": o["neighbourhood_size"], "combinatorial_count": nadj})
json.dump(out, open(sys.argv[2], "w"), indent=1); print(json.dumps(out, indent=0))
