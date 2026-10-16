# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, sys, time
from milp import wdisc
N = int(sys.argv[1]); seed = int(sys.argv[2]); iters = int(sys.argv[3])
rng = np.random.default_rng(seed)
best_overall = 0
t0 = time.time()
for restart in range(int(sys.argv[4]) if len(sys.argv) > 4 else 5):
    rho = rng.permutation(N)
    orders = [np.arange(N), rho]
    w = rng.choice([1.0, rng.uniform(0.4, 1)], N)
    cur, _ = wdisc(orders, w)
    step = 0.25
    for it in range(iters):
        w2 = w.copy()
        mode = rng.random()
        if mode < 0.15:
            # mutate rho: swap two positions
            r2 = rho.copy(); i, j = rng.choice(N, 2, replace=False); r2[i], r2[j] = r2[j], r2[i]
            v, _ = wdisc([np.arange(N), r2], w)
            if v is not None and v >= cur - 1e-9:
                rho, cur = r2, v; orders = [np.arange(N), rho]
            continue
        mask = rng.random(N) < 0.3
        w2[mask] = np.clip(w2[mask] + rng.normal(0, step, mask.sum()), 0, 1)
        v, _ = wdisc(orders, w2)
        if v is not None and v >= cur - 1e-9:
            w, cur = w2, v
        if it % 150 == 149:
            step = max(step * 0.6, 0.01)
    if cur > best_overall:
        best_overall = cur
        print(f"restart {restart} N {N} disc {cur:.4f} t {time.time()-t0:.0f}s rho {rho.tolist()} w {np.round(w,3).tolist()}", flush=True)
print("best", best_overall)
