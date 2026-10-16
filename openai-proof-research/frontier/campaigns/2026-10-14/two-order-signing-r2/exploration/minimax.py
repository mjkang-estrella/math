# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, sys, time, json
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
from milp import wdisc

def rows_of(orders, N):
    R = []
    for o in orders:
        for k in range(N):
            r = np.zeros(N); r[o[:k + 1]] = 1; R.append(r)
    return np.array(R)

def outer(R, E, N, tl=120):
    # vars: w (N), L (1), y[e, r, s] binaries
    m = R.shape[0]
    nE = len(E)
    nv = N + 1 + nE * m * 2
    c = np.zeros(nv); c[N] = -1
    A = lil_matrix((nE * m * 2 + nE, nv))
    lo = []; hi = []
    row = 0
    M = 2.0 * N
    for ei, e in enumerate(E):
        for r in range(m):
            for si, s in enumerate((1, -1)):
                # s * sum_j R[r,j] e_j w_j - L + M*y >= 0   ... i.e. >= L when y=1
                idx = N + 1 + (ei * m + r) * 2 + si
                for j in np.nonzero(R[r])[0]:
                    A[row, j] = s * e[j]
                A[row, N] = -1
                A[row, idx] = -M
                lo.append(-M); hi.append(np.inf)
                # when y=1: s*... - L - M >= -M  -> s*... >= L. when y=0: s*... - L >= -M (always)
                row += 1
        # sum y = 1
        for r in range(m):
            for si in range(2):
                A[row, N + 1 + (ei * m + r) * 2 + si] = 1
        lo.append(1); hi.append(1); row += 1
    integ = np.r_[np.zeros(N + 1), np.ones(nE * m * 2)]
    lb = np.r_[np.zeros(N), 0, np.zeros(nE * m * 2)]
    ub = np.r_[np.ones(N), 2 * N, np.ones(nE * m * 2)]
    res = milp(c, constraints=[LinearConstraint(A.tocsr(), lo, hi)], integrality=integ,
               bounds=Bounds(lb, ub), options={"time_limit": tl, "disp": False})
    return res.x[:N], -res.fun

def run(rho, w0=None, iters=200, log=None):
    N = len(rho)
    orders = [np.arange(N), np.array(rho)]
    R = rows_of(orders, N)
    w = np.ones(N) if w0 is None else np.array(w0, float)
    E = []
    best = (0, None, None)
    for it in range(iters):
        v, eps = wdisc(orders, w)
        if v > best[0]:
            best = (v, w.copy(), eps)
        E.append(eps)
        w, L = outer(R, E, N)
        if log:
            print(f"it {it} inner {v:.4f} outerUB {L:.4f} best {best[0]:.4f}", flush=True)
        if L <= best[0] + 1e-6:
            break
    return best, L

if __name__ == "__main__":
    rho = json.loads(sys.argv[1])
    t0 = time.time()
    best, L = run(rho, iters=int(sys.argv[2]) if len(sys.argv) > 2 else 200, log=True)
    print("FINAL best", best[0], "upper", L, "w", np.round(best[1], 4).tolist(), "time", time.time() - t0)
