# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, itertools, sys
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
N = int(sys.argv[1])
signs = np.array(list(itertools.product([1, -1], repeat=N - 1)))
signs = np.hstack([np.ones((len(signs), 1)), signs])  # fix first sign (global symmetry)

def prefix_matrix(order):
    A = np.zeros((N, N))
    for k in range(N):
        A[k, order[:k + 1]] = 1
    return A

def disc(A, w):
    vals = (signs * w) @ A.T  # (S, rows)
    return np.min(np.max(np.abs(vals), axis=1))

best = 0
for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 200):
    rho = rng.permutation(N)
    A = np.vstack([prefix_matrix(np.arange(N)), prefix_matrix(rho)])
    w = rng.uniform(0.3, 1, N)
    cur = disc(A, w)
    step = 0.2
    for it in range(400):
        w2 = np.clip(w + rng.normal(0, step, N) * (rng.random(N) < 0.4), 0, 1)
        v = disc(A, w2)
        if v >= cur:
            w, cur = w2, v
        if it % 100 == 99:
            step *= 0.5
    if cur > best:
        best = cur
        print(f"trial {trial} disc {cur:.4f} rho {list(rho)} w {np.round(w,3).tolist()}", flush=True)
print("best", best)
