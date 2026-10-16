# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, sys
from vecdisc import rows_of
import cvxpy as cp

def vd(R, w):
    N = len(w)
    B = R * w[None, :]
    G = cp.Variable((N, N), PSD=True); t = cp.Variable()
    prob = cp.Problem(cp.Minimize(t), [cp.diag(G) == 1, cp.diag(B @ G @ B.T) <= t])
    prob.solve(solver="CLARABEL")
    return float(np.sqrt(max(t.value, 0)))

rng = np.random.default_rng(int(sys.argv[2]))
N = int(sys.argv[1])
best = 0
for restart in range(3):
    rho = rng.permutation(N)
    R = rows_of([np.arange(N), rho], N)
    w = rng.uniform(0.5, 1, N); cur = vd(R, w); step = 0.2
    for it in range(150):
        w2 = np.clip(w + rng.normal(0, step, N) * (rng.random(N) < 0.3), 0, 1)
        v = vd(R, w2)
        if v >= cur: w, cur = w2, v
        if it % 50 == 49: step *= 0.5
    best = max(best, cur)
    print(N, restart, round(cur, 4), flush=True)
print("best", best)
