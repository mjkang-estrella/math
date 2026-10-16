# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, cvxpy as cp, sys

def rows_of(orders, N):
    R = []
    for o in orders:
        for k in range(N):
            r = np.zeros(N); r[o[:k + 1]] = 1; R.append(r)
    return np.array(R)

def vecdisc(orders, w):
    N = len(w)
    B = rows_of(orders, N) * w[None, :]
    G = cp.Variable((N, N), PSD=True)
    t = cp.Variable()
    cons = [cp.diag(G) == 1]
    M = B @ G @ B.T
    cons += [cp.diag(M) <= t]
    prob = cp.Problem(cp.Minimize(t), cons)
    prob.solve(solver="CLARABEL")
    return np.sqrt(t.value)

if __name__ == "__main__":
    rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    for N in [16, 32, 64, 128]:
        vals = []
        for trial in range(3):
            rho = rng.permutation(N)
            w = rng.uniform(0, 1, N)
            vals.append(vecdisc([np.arange(N), rho], w))
        # bit-reversal permutation with alternating weights
        L = int(np.log2(N)); br = np.array([int(format(i, f'0{L}b')[::-1], 2) for i in range(N)])
        w2 = np.where(np.arange(N) % 2 == 0, 1.0, 0.5)
        vb = vecdisc([np.arange(N), br], w2)
        print(N, "random", np.round(vals, 3), "bitrev", round(vb, 3), flush=True)
    