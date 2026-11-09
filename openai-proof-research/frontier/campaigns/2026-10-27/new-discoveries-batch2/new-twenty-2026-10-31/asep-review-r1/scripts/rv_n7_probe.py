#!/usr/bin/env python3
"""Optional n = 7 probe (reviewer's own; NOT exhaustive).
(1) Collapse each tight 2-set of x* (source Lemma 8 / Definition 5) to get points of P_ASEP^7; test vertex-ness and
    count adjacent tours exactly.  (2) Random-cost LP vertices of P_ASEP^7 (scipy proposes, exact rank certifies),
    exact adjacent-tour counts.  usage: rv_n7_probe.py SAMPLES SEED OUT.json"""
import sys, json, itertools
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, __import__("os").path.dirname(__file__))
from rv_asep import rank, setup, analyse
X8 = json.load(open(__import__("os").path.join(__import__("os").path.dirname(__file__), "..", "outputs", "xstar-n8-X.json")))
out = {"collapse": [], "random": []}
for S in ([0, 3], [4, 6]):
    keep = [v for v in range(8) if v not in S]; w = len(keep)  # new node w = collapsed S
    lab = {v: k for k, v in enumerate(keep)}
    for v in S: lab[v] = w
    Y = [[0] * 7 for _ in range(7)]
    for i in range(8):
        for j in range(8):
            if lab[i] != lab[j]: Y[lab[i]][lab[j]] += X8[i][j]
    r = analyse(7, Y, 4)
    out["collapse"].append({"S": S, "matrix_times_4": Y, "feasible": r["feasible"], "is_vertex": r["is_vertex"],
                            "vertex_rank": r["vertex_rank"], "num_adjacent_tours": r["num_adjacent_tours"]})
    print(out["collapse"][-1])
n = 7; arcs, idx, m, eqs, cuts, cutrows = setup(n)
A_eq = np.array(eqs, float); A_ub = -np.array(cutrows, float)
rng = np.random.default_rng(int(sys.argv[2])); seen = set()
for s in range(int(sys.argv[1])):
    c = rng.standard_normal(m) if s % 2 else rng.integers(0, 3, m).astype(float) + 1e-3 * rng.standard_normal(m)
    r = linprog(c, A_ub=A_ub, b_ub=-np.ones(len(cutrows)), A_eq=A_eq, b_eq=np.ones(len(eqs)), bounds=(0, None), method="highs-ds")
    x = [F(v).limit_denominator(30) for v in r.x]
    if all(v in (0, 1) for v in x): continue
    L = 1
    for v in x: L = L * v.denominator // __import__("math").gcd(L, v.denominator)
    Y = [[0] * n for _ in range(n)]
    for k, (i, j) in enumerate(arcs): Y[i][j] = int(x[k] * L)
    key = tuple(map(tuple, Y))
    if key in seen: continue
    seen.add(key)
    a = analyse(n, Y, L)
    if not (a["feasible"] and a["is_vertex"]): continue
    out["random"].append({"den": L, "support": a["support_size"], "adj_tours": a["num_adjacent_tours"]})
cnts = [o["adj_tours"] for o in out["random"]]
out["random_summary"] = {"fractional_vertices_tested": len(cnts), "min_adjacent_tours": min(cnts) if cnts else None,
                         "count_with_0": cnts.count(0)}
json.dump(out, open(sys.argv[3], "w"), indent=1); print(out["random_summary"])
