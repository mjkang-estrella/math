"""368807: guided walk on the vertex graph of P_ASEP^n minimising the number of adjacent tours.

Edge step: at vertex v with tight rows I (inequalities) choose I' subset I with rank([Aeq; C_I']) = m-1;
the face {x : Aeq x = 1, C_I' x = d_I'} is a line through v with direction e; if C_i e >= 0 for all i in I
(or for -e) the ray stays in P and stops at the adjacent vertex.  Vertices are rationalised (denominator
limit 10^4) and re-verified (feasibility, rank m tight system).  Adjacency to tours via the rank test of
asep.py.  Simulated-annealing acceptance on the tour-neighbour count among fractional vertices.
usage: asep_walk.py n steps seed
"""
import sys, json, random, resource
import numpy as np
from fractions import Fraction
from scipy.optimize import linprog
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from asep import build, tours

def rationalise(x):
    return np.array([float(Fraction(v).limit_denominator(10000)) for v in x])

def main(n, steps, seed):
    arcs, Aeq, C, d, names = build(n); m = len(arcs); rng = np.random.default_rng(seed); R = random.Random(seed)
    T = tours(n, arcs); tightT = [np.abs(C @ x - d) < 1e-9 for x in T]
    def tight(x): return np.abs(C @ x - d) < 1e-7
    def is_vertex(x):
        return np.all(C @ x - d > -1e-9) and np.allclose(Aeq @ x, 1) and np.linalg.matrix_rank(np.vstack([Aeq, C[tight(x)]])) == m
    def tour_nb(x, cap=10**9):
        I = tight(x); cnt = 0
        for tt in tightT:
            J = I & tt
            if J.sum() < m - 1 - (2 * n - 1): continue  # rank m-1 needs at least m-1-rank(Aeq) inequality rows
            if np.linalg.matrix_rank(np.vstack([Aeq, C[J]])) == m - 1:
                cnt += 1
                if cnt > cap: return cnt
        return cnt
    def frac(x): return bool(np.any(np.abs(x - np.round(x)) > 1e-7))
    # start: LP vertex for a random cost, retry until fractional
    for _ in range(200):
        c = rng.random(m) ** 3
        res = linprog(c, A_ub=-C, b_ub=-d, A_eq=Aeq, b_eq=np.ones(2 * n), bounds=[(0, None)] * m, method='highs-ds')
        x = rationalise(res.x)
        if frac(x) and is_vertex(x): break
    cur, curc = x, tour_nb(x); best = (curc, cur.tolist()); hist = []; visited = set()
    temp = 2.0; zeros = {}; maxzeros = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    for st in range(steps):
        I = np.where(tight(cur))[0]
        # random basis of the tight system: greedy row selection in random order
        order = list(I); R.shuffle(order); basis = []; M = Aeq.copy(); r0 = np.linalg.matrix_rank(M)
        for i in order:
            M2 = np.vstack([M, C[i]]); r2 = np.linalg.matrix_rank(M2)
            if r2 > r0: M, r0 = M2, r2; basis.append(i)
            if r0 == m: break
        drop = R.choice(basis); keep = [i for i in basis if i != drop]
        A2 = np.vstack([Aeq, C[keep]]) if keep else Aeq
        _, s, vt = np.linalg.svd(A2); e = vt[-1]
        moved = False
        for sgn in (1, -1):
            ee = sgn * e
            if np.all(C[I] @ ee > -1e-9):
                slack = C @ cur - d; rate = C @ ee; neg = rate < -1e-9
                if not np.any(neg): continue
                t = np.min(slack[neg] / -rate[neg])
                if t < 1e-9: continue
                nx = rationalise(cur + t * ee)
                if is_vertex(nx): moved = True; break
        if not moved: continue
        key = tuple(np.round(nx, 5))
        if not frac(nx): continue
        c2 = tour_nb(nx, curc + 3)
        if c2 <= curc or R.random() < np.exp(-(c2 - curc) / temp):
            cur, curc = nx, c2
            if key not in visited: visited.add(key); hist.append(c2)
            if c2 < best[0]: best = (c2, nx.tolist())
            if c2 == 0:
                zeros.setdefault(key, nx.tolist())
                if len(zeros) >= maxzeros: break
        temp = max(0.3, temp * 0.995)
    X = [[0.0] * n for _ in range(n)]
    for t, (i, j) in enumerate(arcs): X[i][j] = best[1][t]
    print(json.dumps({'n': n, 'steps': steps, 'seed': seed, 'distinct_fractional_visited': len(visited), 'best_tour_neighbors': best[0],
                      'best_X': [[str(Fraction(v).limit_denominator(10000)) for v in row] for row in X], 'count_hist_tail': hist[-20:], 'zero_vertices': [[[str(Fraction(z[t]).limit_denominator(10000)) if False else None for t in []] for _ in []] or z for z in zeros.values()]}))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
