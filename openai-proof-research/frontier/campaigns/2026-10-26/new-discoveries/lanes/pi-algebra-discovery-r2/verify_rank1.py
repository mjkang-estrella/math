#!/usr/bin/env python3
"""Verify rank-1 reduction of Recht-Re Conjecture 2 at scale.

Rank-1 PSD A_i = v_i v_i^T, operator norm:
  weight(tuple) = prod_{k=1}^{m-1} |<v_{jk}, v_{jk+1}>| * ||v_{j1}|| * ||v_{jm}||
Unit vectors: G = |V V^T| with unit diagonal.
W = sum over all tuples of prod G ; S = sum over distinct tuples.
Check: W/n^m >= S/(n)_m  i.e.  E[walk] >= E[path].
"""
import numpy as np, itertools, sys, math

def walk_path(G, m):
    n = G.shape[0]
    Wv = G.astype(np.float64).copy()
    for _ in range(m - 2):
        Wv = G @ Wv
    W = Wv.sum()
    S = 0.0
    for tup in itertools.permutations(range(n), m):
        p = 1.0
        for k in range(m - 1):
            p *= G[tup[k], tup[k + 1]]
        S += p
    return W, S

def run(seeds=2000, dims=(1,2,3,5,8,16), ns=(4,5,6,8), ms=(4,5,6), worst_report=5):
    worst = []
    rng = np.random.default_rng(7)
    for t in range(seeds):
        d = int(rng.choice(dims)); n = int(rng.choice(ns)); m = int(rng.choice(ms))
        if m > n: continue
        V = rng.standard_normal((n, d))
        V /= np.linalg.norm(V, axis=1, keepdims=True)
        G = np.abs(V @ V.T)
        W, S = walk_path(G, m)
        lhs = W / n**m; rhs = S / (math.factorial(n) / math.factorial(n - m))
        gap = lhs - rhs
        worst.append((gap, d, n, m, t))
        if gap < 0:
            print("*** VIOLATION ***", gap, d, n, m, t)
            np.save(f"rank1_violation_{t}.npy", V)
    worst.sort()
    print("most negative gaps (should be >= 0):")
    for gap, d, n, m, t in worst[:worst_report]:
        print(f"  gap={gap:.3e} d={d} n={n} m={m} trial={t}")
    print("count < 0:", sum(1 for w in worst if w[0] < 0), "of", len(worst))

if __name__ == "__main__":
    run(seeds=int(sys.argv[1]) if len(sys.argv) > 1 else 2000)
