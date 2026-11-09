#!/usr/bin/env python3
"""Adversarial optimization v2 for Recht-Re Conjecture 2 (n=m=4).

A_i = exp(u_i) * O_i diag(s) O_i^T with s unit-scaled shapes, u_i clamped.
Phi = W/256 - S/24. Guards against nan/inf.
"""
import numpy as np, itertools, sys

PERMS = list(itertools.permutations(range(4), 4))
ALLT = list(itertools.product(range(4), repeat=4))

def mats_from_x(x, d=2):
    # x: per matrix: [u_scale, angle, shape logs (d-1 free after fixing product)]
    mats = []
    for i in range(4):
        u = np.clip(x[i * 4], -6, 6)
        ang = x[i * 4 + 1]
        l1 = np.clip(x[i * 4 + 2], -4, 4)
        l2 = np.clip(x[i * 4 + 3], -4, 4)
        O = np.array([[np.cos(ang), -np.sin(ang)], [np.sin(ang), np.cos(ang)]])
        S = np.diag(np.exp([l1, l2]))
        S = S / np.linalg.norm(S @ O.T, 2)  # unit spectral norm shape
        mats.append(np.exp(u) * O @ S @ O.T)
    return mats

def phi_psd(x, d=2):
    mats = mats_from_x(x, d)
    W = 0.0
    Sd = 0.0
    for tup in ALLT:
        P = mats[tup[0]].copy()
        for k in range(1, 4):
            P = P @ mats[tup[k]]
        v = np.linalg.norm(P, 2)
        if not np.isfinite(v):
            return np.nan
        W += v
        if len(set(tup)) == 4:
            Sd += v
    phi = W / 256.0 - Sd / 24.0
    return phi if np.isfinite(phi) else np.nan

def hill_climb(f, x0, iters=6000, scale0=0.25, seed=0):
    rng = np.random.default_rng(seed)
    x = x0.copy(); fx = f(x)
    if np.isnan(fx):
        return np.nan, x
    best_x, best_f = x.copy(), fx
    scale = scale0
    for it in range(iters):
        if it % 80 == 79:
            scale *= 0.93
        xt = x + rng.standard_normal(len(x)) * scale
        ft = f(xt)
        if np.isfinite(ft) and ft < fx:
            x, fx = xt, ft
            if fx < best_f:
                best_x, best_f = x.copy(), fx
                if best_f < 0:
                    return best_f, best_x
    return best_f, best_x

if __name__ == "__main__":
    nrestart = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    best = 1e9
    for restart in range(nrestart):
        rng = np.random.default_rng(5000 + restart)
        x0 = rng.standard_normal(16) * 0.5
        bf, bx = hill_climb(phi_psd, x0, iters=8000, scale0=0.3, seed=restart)
        if np.isfinite(bf) and bf < best:
            best = bf
            print(f"restart {restart}: phi={bf:.8f}", flush=True)
            if bf < 0:
                np.save(f"psd2_hit_{restart}.npy", bx)
                print("*** NEGATIVE ***")
    print("best:", best)
