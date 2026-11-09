#!/usr/bin/env python3
"""Exact check of Recht-Re Conjecture 2 at m=n=4 via convex formulation.

For PSD B_1..B_4, w(t) = ||B_{t1}B_{t2}B_{t3}B_{t4}|| (operator norm).
Conjecture for all scales t_i > 0:
  Phi(t) = (1/256) sum_all w(tuple) prod_k t_{jk} - (1/24) sum_distinct w(d) prod t >= 0.
Equivalent (divide by t1t2t3t4, u = log t):
  F(u) = sum_{repeat tuples} w(t) exp(<e(t)-(1,1,1,1), u>) >= (29/3) * W_D
where e(t) = multiplicity vector. F is convex in u; minimize by gradient descent.
Report min F / ((29/3) W_D) >= 1 ?
"""
import numpy as np, itertools, sys

def psd(d, rng):
    X = rng.standard_normal((d, d)); return X @ X.T

n2 = lambda P: np.linalg.norm(P, 2)

def check(B):
    d = B[0].shape[0]
    W = {}
    for t in itertools.product(range(4), repeat=4):
        P = B[t[0]]
        for k in range(1, 4):
            P = P @ B[t[k]]
        W[t] = n2(P)
    D = [w for k, w in W.items() if len(set(k)) == 4]
    R = [(k, w) for k, w in W.items() if len(set(k)) < 4]
    WD = sum(D)
    target = (29.0 / 3.0) * WD
    # exponent vectors
    E = np.array([[k.count(i) for i in range(4)] for k, w in R])
    wv = np.array([w for k, w in R])
    V = E - 1.0  # e - (1,1,1,1)
    def F(u):
        return float(np.sum(wv * np.exp(V @ u)))
    def grad(u):
        e = np.exp(V @ u)
        return V.T @ (wv * e)
    u = np.zeros(4)
    step = 0.5
    Fv = F(u)
    for it in range(4000):
        g = grad(u)
        gn = np.linalg.norm(g)
        if gn < 1e-14:
            break
        # backtracking
        s = step
        while True:
            un = u - s * g / (gn if gn > 0 else 1)
            # normalize scale (F invariant under u -> u + c*1? no: sum of V rows = e.sum-4 = 0 per tuple, so yes invariant along ones direction)
            Fn = F(un)
            if Fn <= Fv or s < 1e-18:
                break
            s *= 0.5
        if Fn >= Fv - 1e-15 and s < 1e-12:
            u = un; Fv = F(un); break
        u = un; Fv = Fn
    return Fv, target

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
N = int(sys.argv[2]) if len(sys.argv) > 2 else 50
worst = 1e9; wi = None
for t in range(N):
    d = int(rng.choice([2, 3]))
    B = [psd(d, rng) for _ in range(4)]
    Fv, target = check(B)
    r = Fv / target
    if r < worst:
        worst, wi = r, (t, d, Fv, target)
    if r < 1 - 1e-6:
        print("*** CONJECTURE FAIL ***", t, d, Fv, target)
print("worst ratio min F / ((29/3) W_D) (want >= 1):", worst, wi)
