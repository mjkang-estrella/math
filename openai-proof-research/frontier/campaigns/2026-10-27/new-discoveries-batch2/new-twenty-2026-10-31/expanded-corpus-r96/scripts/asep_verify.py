"""368807: exact verification that a given point x is a vertex of P_ASEP^n adjacent to no tour.

Exact integer arithmetic throughout (x and witnesses are scaled to integer vectors by a common denominator).
 (V) vertex: x satisfies every constraint; the tight system [Aeq; C_I(x)] has rank m over Q
     (exact rank by fraction-free elimination over Z).
 (N) for every tour T: with J = I(x) cap I(T), exhibit y in P with C_J y = d_J and y not on the line
     through x and T.  Then the minimal face F_J containing x and T has dimension >= 2, so [x,T] is not
     an edge.  (If F_J were an edge, F_J = [x,T] and y in F_J would lie on that line.)
     y is found by an LP over F_J (HiGHS), rationalised, and then re-checked exactly.
usage: asep_verify.py n vertex.json      (vertex.json: {"X": [[p/q,...],...]})
"""
import sys, json, itertools, resource
from fractions import Fraction
from math import lcm, gcd
import numpy as np
from scipy.optimize import linprog
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))
sys.path.insert(0, __import__('os').path.dirname(__file__))
from asep import build, tours

def int_rank(rows):
    M = [list(r) for r in rows]; rank = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rank, len(M)) if M[i][c] != 0), None)
        if piv is None: continue
        M[rank], M[piv] = M[piv], M[rank]
        for i in range(rank + 1, len(M)):
            if M[i][c]:
                f, g = M[rank][c], M[i][c]
                M[i] = [f * a - g * b for a, b in zip(M[i], M[rank])]  # f != 0, so row space rank is preserved
                gg = 0
                for v in M[i]: gg = gcd(gg, v)
                if gg > 1: M[i] = [v // gg for v in M[i]]
        rank += 1
    return rank

def main(n, path):
    arcs, Aeq, C, d, names = build(n); m = len(arcs)
    X = json.load(open(path))['X']
    xs = [Fraction(X[i][j]) for (i, j) in arcs]
    D = lcm(*[v.denominator for v in xs]); xi = np.array([int(v * D) for v in xs], dtype=np.int64)
    Ci = C.astype(np.int64); di = d.astype(np.int64); Ai = Aeq.astype(np.int64)
    # exact feasibility
    assert np.all(Ai @ xi == D), 'degree equalities fail'
    slack = Ci @ xi - di * D
    assert np.all(slack >= 0), 'infeasible'
    I = slack == 0
    rk = int_rank([list(map(int, r)) for r in np.vstack([Ai, Ci[I]])])
    out = {'n': n, 'denominator': int(D), 'tight_inequalities': int(I.sum()), 'tight_rank_with_equalities': rk, 'is_vertex': rk == m,
           'fractional': bool(np.any(xi % D != 0))}
    T = tours(n, arcs); bad = []; witnesses = 0; rng = np.random.default_rng(0)
    for t, Tx in enumerate(T):
        Ti = Tx.astype(np.int64); IT = (Ci @ Ti - di) == 0; J = I & IT
        ok = False
        for attempt in range(6):
            c = rng.standard_normal(m)
            res = linprog(c, A_ub=-C[~J], b_ub=-d[~J], A_eq=np.vstack([Aeq, C[J]]), b_eq=np.concatenate([np.ones(2 * n), d[J]]),
                          bounds=[(0, None)] * m, method='highs-ds')
            if res.status != 0: continue
            ys = [Fraction(v).limit_denominator(1000) for v in res.x]
            E = lcm(*[v.denominator for v in ys]); yi = np.array([int(v * E) for v in ys], dtype=np.int64)
            if not np.all(Ai @ yi == E): continue
            s2 = Ci @ yi - di * E
            if not (np.all(s2 >= 0) and np.all(s2[J] == 0)): continue
            # non-collinearity of x, T, y: (x - T) and (y - T) linearly independent (2x2 minors over Z)
            u = xi - Ti * D; w = yi - Ti * E  # scaled differences
            minors = np.outer(u, w) - np.outer(w, u)
            if np.any(minors != 0): ok = True; witnesses += 1; break
        if not ok: bad.append(t)
    out.update({'tours': len(T), 'tours_with_noncollinear_witness': witnesses, 'tours_without_certificate': bad[:20], 'n_uncertified': len(bad)})
    print(json.dumps(out))

if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
