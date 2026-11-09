#!/usr/bin/env python3
"""Adversarial optimization for Recht-Re Conjecture 2 violations (n=m=4 focus).

Phi = W/n^m - S/(n)_m ; violation iff Phi < 0.
Search spaces:
  (a) G = |H|, H = L L^T PSD  (rank-1 witnesses A_i = v_i v_i^T)
  (b) general PSD matrices A_i = O_i diag(exp(s)) O_i^T, d=2
"""
import numpy as np, itertools, sys

def perms(n, m):
    return list(itertools.permutations(range(n), m))

def phi_from_G(G, m):
    n = G.shape[0]
    ones = np.ones(n)
    Wm = G.copy()
    for _ in range(m - 2):
        Wm = G @ Wm
    W = ones @ Wm @ ones
    S = 0.0
    for tup in perms(n, m):
        p = 1.0
        for k in range(m - 1):
            p *= G[tup[k], tup[k + 1]]
        S += p
    return W / n**m - S / len(perms(n, m)), W, S

def phi_rank1(L, m):
    H = L @ L.T
    G = np.abs(H)
    return phi_from_G(G, m)[0]

def phi_psd(params, m, d):
    # params: for each of n matrices: angle + d log-scales
    n = len(params)
    mats = []
    for ang, logs in params:
        O = np.array([[np.cos(ang), -np.sin(ang)], [np.sin(ang), np.cos(ang)]])[:d, :d] if d == 2 else None
        S = np.diag(np.exp(logs))
        mats.append(O @ S @ O.T)
    W = 0.0
    prods = {}
    for tup in perms(n, m):
        P = mats[tup[0]]
        for k in range(1, m):
            P = P @ mats[tup[k]]
        W += np.linalg.norm(P, 2)
        prods[tup] = np.linalg.norm(P, 2)
    Sd = sum(v for k, v in prods.items() if len(set(k)) == m)
    return W / n**m - Sd / len(perms(n, m))

def hill_climb(f, x0, iters=4000, scale0=0.3, seed=0):
    rng = np.random.default_rng(seed)
    x = x0.copy(); fx = f(x)
    best_x, best_f = x.copy(), fx
    scale = scale0
    for it in range(iters):
        if it % 50 == 49:
            scale *= 0.9
        xt = x + rng.standard_normal(len(x)) * scale
        ft = f(xt)
        if ft < fx:
            x, fx = xt, ft
            if fx < best_f:
                best_x, best_f = x.copy(), fx
    return best_f, best_x

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "rank1G":
        n, m = 4, 4
        best = 1e9
        for restart in range(int(sys.argv[2]) if len(sys.argv) > 2 else 30):
            L = np.random.default_rng(restart).standard_normal((n, n))
            def f(x):
                return phi_rank1(x.reshape(n, n), m)
            bf, bx = hill_climb(f, L.flatten(), iters=3000, scale0=0.4, seed=restart)
            if bf < best:
                best = bf
                print(f"restart {restart}: phi={bf:.6f}", flush=True)
                if bf < 0:
                    np.save(f"rank1G_hit_{restart}.npy", bx.reshape(n, n))
                    print("*** NEGATIVE ***")
        print("best:", best)
    elif mode == "psd2x2":
        n, m, d = 4, 4, 2
        best = 1e9
        for restart in range(int(sys.argv[2]) if len(sys.argv) > 2 else 20):
            rng = np.random.default_rng(1000 + restart)
            x0 = np.concatenate([np.concatenate([[rng.uniform(0, np.pi)], rng.standard_normal(d) * 0.5]) for _ in range(n)])
            def f(x):
                ps = [(x[i*(1+d)], x[i*(1+d)+1:i*(1+d)+1+d]) for i in range(n)]
                return phi_psd(ps, m, d)
            bf, bx = hill_climb(f, x0, iters=2500, scale0=0.25, seed=restart)
            if bf < best:
                best = bf
                print(f"restart {restart}: phi={bf:.6f}", flush=True)
                if bf < 0:
                    np.save(f"psd_hit_{restart}.npy", bx)
                    print("*** NEGATIVE ***")
        print("best:", best)
