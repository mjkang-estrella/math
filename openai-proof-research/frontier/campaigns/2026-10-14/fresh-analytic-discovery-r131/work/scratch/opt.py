import json
import sys
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from rnum import R, cn


def f(x, n, N):
    V = x.reshape(N, n)
    try:
        return -R(V) / cn(n)
    except Exception:
        return 0.0


def run(args):
    n, N, seed, mode = args
    rng = np.random.default_rng(seed)
    if mode == "simplex":
        S = np.vstack([np.zeros(n), np.eye(n)])
        extra = rng.dirichlet(np.ones(n + 1), N - n - 1) @ S
        V = np.vstack([S, extra]) + 0.05 * rng.standard_normal((N, n))
    elif mode == "gauss":
        V = rng.standard_normal((N, n))
    else:
        V = rng.random((N, n))
    best = None
    x = V.ravel()
    for it in range(4):
        res = minimize(f, x, args=(n, N), method="Powell", options={"maxiter": 20000, "xtol": 1e-7, "ftol": 1e-10})
        x = res.x
        if best is None or res.fun < best[0] - 1e-12:
            best = (res.fun, x.copy())
        else:
            break
        x = x + 1e-3 * rng.standard_normal(x.shape)
    return (n, N, seed, mode, -best[0], best[1].tolist())


if __name__ == "__main__":
    n = int(sys.argv[1])
    Ns = [int(a) for a in sys.argv[2].split(",")]
    reps = int(sys.argv[3])
    out = sys.argv[4]
    tasks = [(n, N, s, m) for N in Ns for s in range(reps) for m in ("simplex", "gauss", "unif")]
    with Pool(30) as p:
        res = p.map(run, tasks)
    res.sort(key=lambda r: -r[4])
    for r in res[:15]:
        print(r[0], r[1], r[2], r[3], round(r[4], 6))
    json.dump(res, open(out, "w"))
