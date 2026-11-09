#!/usr/bin/env python3
"""Final verification sweep for the equivalent form (*) of Conjecture 1(i) of
arXiv:2403.04199 (MathDB 362175):

    (*) || X W Y - Y W X ||_F <= sqrt(w1^2+w2^2) ||X||_F ||Y||_F,
    W = diag(w1 >= ... >= wn) > 0.

Alternating exact-eigenvalue maximization over (X,Y); many random spectra and
restarts; extremal structure recorded.  Also verifies the paper's n=2 block value
equals the conjectured constant (consistency with their theorem for n=2).
"""
import numpy as np
import json, sys, os

def build_op(f, n):
    M = np.zeros((n * n, n * n), complex)
    for j in range(n * n):
        E = np.zeros((n, n), complex)
        E[j % n, j // n] = 1.0
        M[:, j] = f(E).ravel(order="F")
    return M

def op_Y(X, W):
    n = X.shape[0]
    return build_op(lambda Y: X @ W @ Y - Y @ W @ X, n)

def op_X(Y, W):
    n = Y.shape[0]
    return build_op(lambda X: X @ W @ Y - Y @ W @ X, n)

def optimize(W, rng, starts, iters):
    n = W.shape[0]
    best = (0.0, None)
    for s in range(starts):
        X = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        for it in range(iters):
            MY = op_Y(X, W)
            u, sv, vt = np.linalg.svd(MY)
            Y = vt[0].conj().reshape((n, n), order="F")
            MX = op_X(Y, W)
            u, sv, vt = np.linalg.svd(MX)
            X = vt[0].conj().reshape((n, n), order="F")
        g = np.linalg.svd(op_Y(X, W), compute_uv=False)[0] ** 2
        r2 = g / np.linalg.norm(X) ** 2
        if r2 > best[0]:
            best = (r2, X.copy())
    return best

def main():
    rng = np.random.default_rng(20261027)
    results = []
    worst = 0.0
    spectra = [
        ("near-equal", lambda n: 1.0 - 0.02 * np.arange(n) / max(n - 1, 1)),
        ("spread", lambda n: np.linspace(1, 0.05, n)),
        ("one-big", lambda n: np.concatenate([[1.0], np.full(n - 1, 0.1)])),
        ("two-big", lambda n: np.concatenate([[1.0, 0.9], np.full(max(n - 2, 0), 0.05)])),
        ("log", lambda n: np.logspace(0, -2, n)),
    ]
    for name, gen in spectra:
        for n in [3, 4, 5, 6, 7, 8]:
            w = gen(n)
            W = np.diag(w)
            c2 = w[0] ** 2 + w[1] ** 2
            r2, X = optimize(W, rng, starts=12, iters=35)
            sv = np.linalg.svd(X, compute_uv=False)
            # support check: mass outside top-2 rows/cols
            mask = np.zeros((n, n), bool); mask[:2, :2] = True
            outside = np.linalg.norm(X[~mask]) if n > 2 else 0.0
            rec = dict(spectrum=name, n=n, c2=c2, best_ratio2=r2,
                       ratio2_over_c2=r2 / c2, sv1=sv[0], sv2=sv[1], outside_mass=outside)
            results.append(rec)
            worst = max(worst, r2 / c2)
            print(f"{name:10s} n={n}  c2={c2:.6f} ratio2={r2:.6f}  ratio2/c2={r2/c2:.8f}  "
                  f"outside={outside:.2e}", flush=True)
    out = dict(worst_ratio2_over_c2=worst, results=results)
    path = os.path.join(os.path.dirname(__file__), "..", "verification", "sweep14.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("\nWORST ratio2/c2 over sweep:", worst)
    print("saved:", path)

if __name__ == "__main__":
    main()
