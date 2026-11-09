"""368807: neighborhood-tour conjecture for ASEP vertices (arXiv:2506.10671, Conjecture 1).

P_ASEP^n = { x in R^{n(n-1)} : sum_i x_ij = 1 (all j), sum_j x_ij = 1 (all i),
             sum_{i in S, j not in S} x_ij >= 1 for all S with 2 <= |S| <= n-2, x >= 0 }   (source (2)-(4),(6)).
Vertices u, v are adjacent iff the face cut out by the constraints tight at both is 1-dimensional,
i.e. rank([A_eq; C_{I(u) cap I(v)}]) = m - 1, where m = n(n-1).
Vertices are sampled as LP optima for random cost vectors (HiGHS); each is then checked against all
directed Hamiltonian cycles (tours).  Floating-point screening only; any failure must be re-certified exactly.
usage: asep.py n samples seed [costmode]
"""
import sys, itertools, json, random, resource
import numpy as np
from scipy.optimize import linprog
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))

def build(n):
    arcs = [(i, j) for i in range(n) for j in range(n) if i != j]; m = len(arcs); idx = {a: t for t, a in enumerate(arcs)}
    Aeq = []
    for j in range(n): Aeq.append([1.0 if a[1] == j else 0.0 for a in arcs])
    for i in range(n): Aeq.append([1.0 if a[0] == i else 0.0 for a in arcs])
    C = []; names = []  # rows of C x >= d
    for s in range(2, n - 1):
        for S in itertools.combinations(range(n), s):
            Ss = set(S); C.append([1.0 if (a[0] in Ss and a[1] not in Ss) else 0.0 for a in arcs]); names.append(('cut', S))
    for t in range(m):
        r = [0.0] * m; r[t] = 1.0; C.append(r); names.append(('nonneg', arcs[t]))
    d = [1.0 if nm[0] == 'cut' else 0.0 for nm in names]
    return arcs, np.array(Aeq), np.array(C), np.array(d), names

def tours(n, arcs):
    idx = {a: t for t, a in enumerate(arcs)}; out = []
    for perm in itertools.permutations(range(1, n)):
        cyc = (0,) + perm; x = np.zeros(len(arcs))
        for t in range(n): x[idx[(cyc[t], cyc[(t + 1) % n])]] = 1.0
        out.append(x)
    return out

def main(n, samples, seed, costmode='uniform'):
    arcs, Aeq, C, d, names = build(n); m = len(arcs); rnd = np.random.default_rng(seed)
    T = tours(n, arcs); tight_T = [np.abs(C @ x - d) < 1e-9 for x in T]
    rankA = np.linalg.matrix_rank(Aeq)
    lows = []; seen = {}; fails = []; stats = {'samples': samples, 'distinct_vertices': 0, 'fractional': 0, 'min_tour_neighbors': None}
    for s in range(samples):
        if costmode == 'uniform': c = rnd.random(m)
        elif costmode == 'exp': c = rnd.exponential(size=m)
        else: c = rnd.integers(0, 4, size=m).astype(float) + 1e-3 * rnd.random(m)
        res = linprog(c, A_ub=-C, b_ub=-d, A_eq=Aeq, b_eq=np.ones(2 * n), bounds=[(0, None)] * m, method='highs-ds')
        if res.status != 0: continue
        x = np.round(res.x * 840) / 840  # denominators of small ASEP vertices divide 840 in practice; checked below
        if np.max(np.abs(x - res.x)) > 1e-7: x = res.x
        key = tuple(np.round(x, 6))
        if key in seen: continue
        tight = np.abs(C @ x - d) < 1e-7
        # vertex check: tight constraints together with Aeq have rank m
        rk = np.linalg.matrix_rank(np.vstack([Aeq, C[tight]]))
        if rk != m: continue
        frac = bool(np.any(np.abs(x - np.round(x)) > 1e-7))
        cnt = 0
        if frac:
            for tt in tight_T:
                inter = tight & tt
                if np.linalg.matrix_rank(np.vstack([Aeq, C[inter]])) == m - 1: cnt += 1
            if cnt == 0: fails.append([float(v) for v in x])
            stats['fractional'] += 1
            if stats['min_tour_neighbors'] is None or cnt < stats['min_tour_neighbors']: stats['min_tour_neighbors'] = cnt
        seen[key] = cnt
        if frac: lows.append((cnt, [float(v) for v in x]))
    stats['distinct_vertices'] = len(seen); stats['failures'] = fails[:3]; stats['n_failures'] = len(fails); stats['n'] = n
    stats['tour_neighbor_histogram'] = {str(k): sum(1 for v in seen.values() if v == k) for k in sorted(set(seen.values()))}
    lows.sort(key=lambda t: t[0]); stats['lowest'] = [{'tour_neighbors': c, 'X': [[next((x[t] for t, a in enumerate(arcs) if a == (i, j)), 0.0) for j in range(n)] for i in range(n)]} for c, x in lows[:4]]
    print(json.dumps(stats))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else 'uniform')
