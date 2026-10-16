# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix, vstack, hstack, tril

def prefix_rows(order, N):
    # rows k: indicator of first k+1 elements of order
    rows, cols = [], []
    for k in range(N):
        for j in order[:k + 1]:
            rows.append(k); cols.append(j)
    return csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N))

def wdisc(orders, w, time_limit=60):
    """min_eps max over prefixes of all orders |sum w eps|; returns (value, eps)."""
    N = len(w)
    A = vstack([prefix_rows(o, N) for o in orders]).tocsr()
    AW = A.multiply(w.reshape(1, -1)).tocsr()
    m = AW.shape[0]
    rowsum = np.asarray(AW.sum(axis=1)).ravel()
    # eps = 2z-1 ; AW eps = 2 AW z - rowsum ; constraints -t <= 2AWz - rowsum <= t
    ones = csr_matrix(np.ones((m, 1)))
    C1 = hstack([2 * AW, -ones])   # 2AWz - t <= rowsum
    C2 = hstack([2 * AW, ones])    # 2AWz + t >= rowsum
    c = np.zeros(N + 1); c[-1] = 1
    cons = [LinearConstraint(C1, -np.inf, rowsum), LinearConstraint(C2, rowsum, np.inf)]
    integrality = np.r_[np.ones(N), 0]
    lb = np.r_[np.zeros(N), 0]; ub = np.r_[np.ones(N), np.inf]
    # symmetry: fix z_0 = 1
    lb[0] = 1
    res = milp(c, constraints=cons, integrality=integrality, bounds=Bounds(lb, ub),
               options={"time_limit": time_limit, "disp": False})
    if res.x is None:
        return None, None
    z = np.round(res.x[:N])
    eps = 2 * z - 1
    return res.fun, eps

def check(orders, w, eps):
    best = 0
    for o in orders:
        s = np.cumsum(w[o] * eps[o])
        best = max(best, np.max(np.abs(s)))
    return best
