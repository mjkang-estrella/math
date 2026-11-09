#!/usr/bin/env python3
"""n = 5 fidelity control for Definition 3 (reviewer's own).
Finds vertices of P_ASEP^5 with random-cost LPs (scipy HiGHS, floating point used ONLY to propose points),
rationalises them, certifies each exactly as a vertex (feasibility + tight rank 20, exact integer rank),
closes under the S_5 action, and then counts, for one representative per orbit, the number of vertices
adjacent to it in the polytope's vertex-edge graph (exact rank of common tight system = 19).
Compare with the source's Table 2: orbit sizes 60,120,60,120,24 (total 384), |N(x)| = 28,20,28,23,148,
tight sets 6,4,4,4,10.  usage: rv_n5_table2.py SAMPLES SEED OUT.json"""
import sys, json, itertools, random
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, __import__("os").path.dirname(__file__))
from rv_asep import rank, setup
n = 5; arcs, idx, m, eqs, cuts, cutrows = setup(n)
samples = int(sys.argv[1]); random.seed(int(sys.argv[2])); rng = np.random.default_rng(int(sys.argv[2]))
A_eq = np.array(eqs, float); b_eq = np.ones(len(eqs)); A_ub = -np.array(cutrows, float); b_ub = -np.ones(len(cutrows))
def tightinfo(x):
    zero = [k for k in range(m) if x[k] == 0]
    tc = [s for s in range(len(cuts)) if sum(x[k] for k in range(m) if cutrows[s][k]) == 1]
    return zero, tc
def is_vertex(x):
    if any(v < 0 for v in x): return False
    if any(sum(x[k] for k in range(m) if r[k]) != 1 for r in eqs): return False
    if any(sum(x[k] for k in range(m) if r[k]) < 1 for r in cutrows): return False
    zero, tc = tightinfo(x)
    unit = lambda k: [1 if t == k else 0 for t in range(m)]
    return rank(eqs + [unit(k) for k in zero] + [cutrows[s] for s in tc], m) == m
def act(p, x):  # x'_{p(i)p(j)} = x_ij
    y = [None] * m
    for k, (i, j) in enumerate(arcs): y[idx[(p[i], p[j])]] = x[k]
    return tuple(y)
V = set(); bad = 0
for s in range(samples):
    c = rng.standard_normal(m)
    r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, None), method="highs-ds")
    x = tuple(F(v).limit_denominator(12) for v in r.x)
    if x in V: continue
    if is_vertex(list(x)):
        for p in itertools.permutations(range(n)): V.add(act(p, x))
    else: bad += 1
V = sorted(V)
# orbits
orbits = []; seen = set()
for x in V:
    if x in seen: continue
    O = {act(p, x) for p in itertools.permutations(range(n))}; seen |= O; orbits.append((x, len(O)))
unit = lambda k: [1 if t == k else 0 for t in range(m)]
info = {x: tightinfo(x) for x in V}
out = {"samples": samples, "rationalisation_rejects": bad, "num_vertices": len(V), "orbits": []}
for x, size in orbits:
    zx, tx = info[x]; zs, ts = set(zx), set(tx); nadj = 0; ntour_adj = 0
    for y in V:
        if y == x: continue
        zy, ty = info[y]
        J = [unit(k) for k in zx if k in set(zy)] + [cutrows[s] for s in tx if s in set(ty)]
        if rank(eqs + J, m) == m - 1:
            nadj += 1
            if all(v in (0, 1) for v in y): ntour_adj += 1
    vals = sorted(set(x)); freq = {str(v): x.count(v) for v in vals}
    out["orbits"].append({"orbit_size": size, "values": freq, "tight_sets": len(tx), "neighbourhood_size": nadj,
                          "adjacent_tours": ntour_adj, "is_tour": all(v in (0, 1) for v in x),
                          "rep": [str(v) for v in x]})
out["orbits"].sort(key=lambda o: (o["orbit_size"], o["neighbourhood_size"]))
json.dump(out, open(sys.argv[3], "w"), indent=1)
print(json.dumps({k: v for k, v in out.items() if k != "orbits"}))
for o in out["orbits"]: print({k: v for k, v in o.items() if k != "rep"})
