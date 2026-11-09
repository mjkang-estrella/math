#!/usr/bin/env python3
"""Search for violations of Recht-Re Conjecture 2 (norm-sum), MathDB 346741.

Claim (open for m>=4): (1/n^m) sum_all ||A_{j1}...A_{jm}|| >= (1/(n)_m) sum_distinct ||...||.
Equivalently: average weight over all ordered m-tuples >= average over injective tuples.

Rank-1 PSD (A_i = v_i v_i^T, spectral norm): weight = prod |<v_{jk},v_{jk+1}>|.
General PSD: spectral norm of the product.
"""
import numpy as np
import itertools, sys

rng = np.random.default_rng(20261026)

def rank1_stats(V, m):
    """V: (n,d) rows are vectors. Returns W (all-tuple sum), S (distinct sum), counts."""
    n = V.shape[0]
    G = np.abs(V @ V.T)
    # walk sum: sum over j1..jm of prod_{k=1}^{m-1} G_{jk jk+1} = 1^T G^{m-1} 1
    ones = np.ones(n)
    Wv = G.copy()
    for _ in range(m - 2):
        Wv = G @ Wv
    W = ones @ Wv @ ones  # sum over all walks
    S = 0.0
    for tup in itertools.permutations(range(n), m):
        p = 1.0
        for k in range(m - 1):
            p *= G[tup[k], tup[k + 1]]
        S += p
    return W, S, n**m, len(list(itertools.permutations(range(n), m)))

def phi(W, S, cnt_all, cnt_dist):
    return W / cnt_all - S / cnt_dist

def check_rank1(trials=2000, dims=(2, 3, 4, 8), ns=(4,), ms=(4,), scale=False):
    best = 1e9
    for d in dims:
        for n in ns:
            for m in ms:
                if m > n:
                    continue
                for t in range(trials):
                    V = rng.standard_normal((n, d))
                    V /= np.linalg.norm(V, axis=1, keepdims=True)
                    if scale:
                        V *= np.exp(rng.standard_normal((n, 1)) * 1.5)
                    W, S, ca, cd = rank1_stats(V, m)
                    f = phi(W, S, ca, cd)
                    if f < best:
                        best = f
                        print(f"rank1 d={d} n={n} m={m} trial={t} phi={f:.6f} W={W:.4f} S={S:.4f} ratio_walk/path={W/ca:.6f} vs {S/cd:.6f}", flush=True)
                        if f < 0:
                            np.save(f"rank1_hit_d{d}_n{n}_m{m}.npy", V)
                            print("*** NEGATIVE PHI ***")
    return best

def psd_stats(mats, m):
    n = len(mats)
    assert m <= n
    Wall = 0.0
    for tup in itertools.product(range(n), repeat=m):
        P = mats[tup[0]]
        for k in range(1, m):
            P = P @ mats[tup[k]]
        Wall += np.linalg.norm(P, 2)
    Sdist = 0.0
    for tup in itertools.permutations(range(n), m):
        P = mats[tup[0]]
        for k in range(1, m):
            P = P @ mats[tup[k]]
        Sdist += np.linalg.norm(P, 2)
    return Wall, Sdist, n**m, len(list(itertools.permutations(range(n), m)))

def check_psd(trials=200, dims=(2, 3), ns=(4,), ms=(4,), wishart_scale=1.0):
    best = 1e9
    for d in dims:
        for n in ns:
            for m in ms:
                for t in range(trials):
                    mats = []
                    for i in range(n):
                        B = rng.standard_normal((d, d)) * wishart_scale
                        mats.append(B @ B.T)
                    W, S, ca, cd = psd_stats(mats, m)
                    f = phi(W, S, ca, cd)
                    if f < best:
                        best = f
                        print(f"psd d={d} n={n} m={m} trial={t} phi={f:.6f}", flush=True)
                        if f < 0:
                            np.save(f"psd_hit_d{d}_n{n}_m{m}.npy", np.array(mats))
                            print("*** NEGATIVE PHI ***")
    return best

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "rank1"
    if mode == "rank1":
        check_rank1(trials=int(sys.argv[2]) if len(sys.argv) > 2 else 500)
    elif mode == "psd":
        check_psd(trials=int(sys.argv[2]) if len(sys.argv) > 2 else 50)
    elif mode == "rank1scaled":
        check_rank1(trials=500, dims=(2, 3), ns=(4,), ms=(4,), scale=True)
    elif mode == "psd5":
        check_psd(trials=20, dims=(2, 3), ns=(5,), ms=(5,))
