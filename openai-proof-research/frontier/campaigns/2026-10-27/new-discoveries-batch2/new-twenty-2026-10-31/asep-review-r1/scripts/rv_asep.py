#!/usr/bin/env python3
"""Reviewer's own exact checker for P_ASEP^n (stdlib only; shares no code with the author lane).
usage: rv_asep.py n MATRIX_JSON DEN OUT.json
MATRIX_JSON: integer n x n matrix X (x = X/DEN). Checks feasibility, tight sets, vertex rank, and for every
tour T (all (n-1)! cyclic orders starting at node 0) the rank of the constraints tight at both x and T."""
import sys, json, itertools, collections
from fractions import Fraction

def rank(rows, ncol):
    """Exact rank over Q of integer rows (fraction-free elimination with gcd normalisation)."""
    from math import gcd
    M = [list(r) for r in rows if any(r)]
    rk = 0; col = 0
    while M and col < ncol:
        piv = next((k for k, r in enumerate(M) if r[col] != 0), None)
        if piv is None: col += 1; continue
        P = M.pop(piv); p = P[col]; NM = []
        for r in M:
            c = r[col]
            if c:
                r = [p * a - c * b for a, b in zip(r, P)]
                g = 0
                for a in r: g = gcd(g, a)
                if g > 1: r = [a // g for a in r]
            if any(r): NM.append(r)
        M = NM; rk += 1; col += 1
    return rk

def setup(n):
    arcs = [(i, j) for i in range(n) for j in range(n) if i != j]
    idx = {a: k for k, a in enumerate(arcs)}
    m = len(arcs)
    eqs = []
    for j in range(n):  # (2) in-degree
        r = [0] * m
        for i in range(n):
            if i != j: r[idx[(i, j)]] = 1
        eqs.append(r)
    for i in range(n):  # (3) out-degree
        r = [0] * m
        for j in range(n):
            if i != j: r[idx[(i, j)]] = 1
        eqs.append(r)
    cuts = [frozenset(S) for k in range(2, n - 1) for S in itertools.combinations(range(n), k)]  # (4) 2<=|S|<=n-2
    cutrows = []
    for S in cuts:
        r = [0] * m
        for (i, j) in arcs:
            if i in S and j not in S: r[idx[(i, j)]] = 1
        cutrows.append(r)
    return arcs, idx, m, eqs, cuts, cutrows

def analyse(n, X, den):
    arcs, idx, m, eqs, cuts, cutrows = setup(n)
    x = [Fraction(X[i][j], den) for (i, j) in arcs]
    out = {"n": n, "m": m, "num_cuts": len(cuts)}
    assert all(X[i][i] == 0 for i in range(n)), "nonzero diagonal"
    feas = all(v >= 0 for v in x)
    feas &= all(sum(x[k] for k, v in enumerate(r) if v) == 1 for r in eqs)
    cutval = [sum(x[k] for k, v in enumerate(r) if v) for r in cutrows]
    feas &= all(c >= 1 for c in cutval)
    out["feasible"] = bool(feas)
    zero = [k for k in range(m) if x[k] == 0]
    tight = [s for s in range(len(cuts)) if cutval[s] == 1]
    out["support_size"] = m - len(zero)
    out["tight_cuts"] = [sorted(cuts[s]) for s in tight]
    out["min_positive_entry"] = str(min(v for v in x if v > 0))
    out["min_nontight_cut"] = str(min((c for c in cutval if c > 1), default=None))
    unit = lambda k: [1 if t == k else 0 for t in range(m)]
    out["vertex_rank"] = rank(eqs + [unit(k) for k in zero] + [cutrows[s] for s in tight], m)
    out["is_vertex"] = out["vertex_rank"] == m
    # all tours: cyclic orders 0, p1..p_{n-1}
    hist = collections.Counter(); adj = []; ntour = 0
    for perm in itertools.permutations(range(1, n)):
        order = (0,) + perm
        succ = {order[k]: order[(k + 1) % n] for k in range(n)}
        T = set((i, succ[i]) for i in range(n))
        ntour += 1
        J0 = [unit(k) for k in zero if arcs[k] not in T]
        Jc = [cutrows[s] for s in tight if sum(1 for i in cuts[s] if succ[i] not in cuts[s]) == 1]
        rk = rank(eqs + J0 + Jc, m)
        hist[rk] += 1
        if rk == m - 1: adj.append(list(order))
    out["num_tours"] = ntour
    out["rank_histogram"] = {str(k): hist[k] for k in sorted(hist)}
    out["max_common_rank"] = max(hist)
    out["adjacent_tours"] = adj
    out["num_adjacent_tours"] = len(adj)
    return out

if __name__ == "__main__":
    n = int(sys.argv[1]); X = json.load(open(sys.argv[2])); den = int(sys.argv[3])
    res = analyse(n, X, den)
    json.dump(res, open(sys.argv[4], "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "adjacent_tours"}))
