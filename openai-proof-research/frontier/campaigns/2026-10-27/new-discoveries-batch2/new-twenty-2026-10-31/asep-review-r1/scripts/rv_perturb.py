#!/usr/bin/env python3
"""Second, structurally different check (reviewer's own, stdlib only).
For each tour T: compute an exact rational nullspace basis of the system tight at both x and T
(Fraction Gauss-Jordan, independent of rv_asep.rank), confirm nullity >= 2, pick a basis vector v not
parallel to x - T, choose eps from the exact slacks, and verify z +- eps*v in P_ASEP^n by evaluating
ALL constraints exactly, where z = (x+T)/2. This directly witnesses that [x,T] is not a face.
Also recomputes the rank modulo the prime 1000003 as a third, lower-bound check.
usage: rv_perturb.py n MATRIX_JSON DEN OUT.json [LO HI]  (tour index range in itertools order)"""
import sys, json, itertools
from fractions import Fraction as F
n = int(sys.argv[1]); X = json.load(open(sys.argv[2])); den = int(sys.argv[3])
arcs = [(i, j) for i in range(n) for j in range(n) if i != j]; m = len(arcs)
cuts = [frozenset(S) for k in range(2, n - 1) for S in itertools.combinations(range(n), k)]
x = {a: F(X[a[0]][a[1]], den) for a in arcs}
def cutv(y, S): return sum(y[(i, j)] for (i, j) in arcs if i in S and j not in S)
def feasible(y):
    if any(y[a] < 0 for a in arcs): return False
    for v in range(n):
        if sum(y[(i, v)] for i in range(n) if i != v) != 1: return False
        if sum(y[(v, j)] for j in range(n) if j != v) != 1: return False
    return all(cutv(y, S) >= 1 for S in cuts)
assert feasible(x)
xt = [S for S in cuts if cutv(x, S) == 1]
def nullspace(rows):
    A = [[F(c) for c in r] for r in rows]; piv = []; r0 = 0
    for c in range(m):
        p = next((k for k in range(r0, len(A)) if A[k][c] != 0), None)
        if p is None: continue
        A[r0], A[p] = A[p], A[r0]; pv = A[r0][c]; A[r0] = [a / pv for a in A[r0]]
        for k in range(len(A)):
            if k != r0 and A[k][c] != 0:
                f = A[k][c]; A[k] = [a - f * b for a, b in zip(A[k], A[r0])]
        piv.append(c); r0 += 1
        if r0 == len(A): break
    free = [c for c in range(m) if c not in piv]; basis = []
    for fc in free:
        v = [F(0)] * m; v[fc] = F(1)
        for k, pc in enumerate(piv): v[pc] = -A[k][fc]
        basis.append(v)
    return len(piv), basis
def rank_modp(rows, p=1000003):
    A = [[c % p for c in r] for r in rows]; rk = 0
    for c in range(m):
        q = next((k for k in range(rk, len(A)) if A[k][c]), None)
        if q is None: continue
        A[rk], A[q] = A[q], A[rk]; inv = pow(A[rk][c], p - 2, p); A[rk] = [a * inv % p for a in A[rk]]
        for k in range(len(A)):
            if k != rk and A[k][c]:
                f = A[k][c]; A[k] = [(a - f * b) % p for a, b in zip(A[k], A[rk])]
        rk += 1
    return rk
res = {"tours": 0, "nonface_witnessed": 0, "min_nullity": None, "rank_q_eq_rank_p": True, "fail": []}
LO = int(sys.argv[5]) if len(sys.argv) > 5 else 0; HI = int(sys.argv[6]) if len(sys.argv) > 6 else 10**9
res["range"] = [LO, HI]
for ti, perm in enumerate(itertools.permutations(range(1, n))):
    if not (LO <= ti < HI): continue
    order = (0,) + perm; succ = {order[k]: order[(k + 1) % n] for k in range(n)}
    T = {a: F(1 if succ[a[0]] == a[1] else 0) for a in arcs}
    rows = []
    for v in range(n):
        rows.append([1 if a[1] == v else 0 for a in arcs]); rows.append([1 if a[0] == v else 0 for a in arcs])
    for a in arcs:
        if x[a] == 0 and T[a] == 0: rows.append([1 if b == a else 0 for b in arcs])
    for S in xt:
        if cutv(T, S) == 1: rows.append([1 if (b[0] in S and b[1] not in S) else 0 for b in arcs])
    rk, basis = nullspace(rows)
    if rank_modp(rows) != rk: res["rank_q_eq_rank_p"] = False
    res["tours"] += 1
    res["min_nullity"] = len(basis) if res["min_nullity"] is None else min(res["min_nullity"], len(basis))
    d = [x[a] - T[a] for a in arcs]
    # choose v in the nullspace not parallel to d
    vv = None
    for b in basis:
        k = next(t for t in range(m) if d[t] != 0); lam = b[k] / d[k]
        if any(b[t] != lam * d[t] for t in range(m)): vv = b; break
    if vv is None: res["fail"].append(list(order)); continue
    v = dict(zip(arcs, vv)); z = {a: (x[a] + T[a]) / 2 for a in arcs}
    # exact eps: half the minimal ratio slack/|change| over non-tight constraints
    ratios = []
    for a in arcs:
        if v[a] != 0 and z[a] > 0: ratios.append(z[a] / abs(v[a]))
    for S in cuts:
        dv = cutv(v, S); sl = cutv(z, S) - 1
        if dv != 0 and sl > 0: ratios.append(sl / abs(dv))
    eps = min(ratios) / 2
    ok = all(feasible({a: z[a] + s * eps * v[a] for a in arcs}) for s in (1, -1))
    if ok: res["nonface_witnessed"] += 1
    else: res["fail"].append(list(order))
json.dump(res, open(sys.argv[4], "w"), indent=1); print(json.dumps(res))
