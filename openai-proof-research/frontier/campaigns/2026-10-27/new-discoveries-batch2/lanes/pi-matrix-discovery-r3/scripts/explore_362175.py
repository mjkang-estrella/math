#!/usr/bin/env python3
"""
Numerical investigation of the equivalent form of Conjecture 1(i) (ineq (14)) of
arXiv:2403.04199 (MathDB 362175):

    (*) || X W Y - Y W X ||_F <= sqrt(w1^2 + w2^2) ||X||_F ||Y||_F

W = diag(w_1 >= ... >= w_n) > 0.  sup over X,Y computed by alternating maximization
(each substep is an exact top-eigenvalue problem; the bilinear map is linear in each
argument).  Operators are built EXPLICITLY by applying to basis matrices with
column-stacking vectorization (vec(PYQ) = (Q^T kron P) vec(Y) convention checked).
"""
import numpy as np

def build_op(f, n):
    """Matrix of linear map f on n x n complex matrices, column-stacking.
    Column-stacking index j <-> (row j % n, col j // n)."""
    M = np.zeros((n * n, n * n), complex)
    for j in range(n * n):
        E = np.zeros((n, n), complex)
        E[j % n, j // n] = 1.0
        M[:, j] = f(E).ravel(order="F")
    return M

def op_Y(X, W):
    n = len(W)
    return build_op(lambda Y: X @ W @ Y - Y @ W @ X, n)

def op_X(Y, W):
    n = len(W)
    return build_op(lambda X: X @ W @ Y - Y @ W @ X, n)

def opnorm2(M):
    return float(np.linalg.svd(M, compute_uv=False)[0]) ** 2

def optimize_ratio(W, rng, starts=30, iters=50):
    n = len(W)
    best = (0.0, None)
    for s in range(starts):
        X = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
        g = 0.0
        for it in range(iters):
            MY = op_Y(X, W) if it == 0 else MY
            # Y-update: top right singular vector direction
            u, sv, vt = np.linalg.svd(MY)
            Y = vt[0].conj().reshape((n, n), order="F")  # top singular vector
            MX = op_X(Y, W)
            u, sv, vt = np.linalg.svd(MX)
            X = vt[0].conj().reshape((n, n), order="F")
            MY = op_Y(X, W)
            g = sv[0] ** 2 if False else opnorm2(MY)
        # final exact evaluation with ||X|| = ||Y|| = 1 directions
        u, sv, vt = np.linalg.svd(MY)
        g = sv[0] ** 2
        # X currently unit Frobenius (from singular vector); ratio^2 = g/||X||^2
        nX = np.linalg.norm(X)
        if nX < 1e-12:
            continue
        if g / nX**2 > best[0]:
            best = (g / nX**2, X.copy())
    return best

def run(W, label, seeds=2, starts=20, iters=40):
    n = len(W)
    W = np.diag(W)
    c2 = W[0, 0] ** 2 + W[1, 1] ** 2
    best_ratio2 = 0.0
    best_X = None
    for sd in range(seeds):
        rng = np.random.default_rng(1000 * sd + 17)
        r2, X = optimize_ratio(W, rng, starts=starts, iters=iters)
        if X is not None and r2 > best_ratio2:
            best_ratio2, best_X = r2, X
    print(f"n={n} {label:26s} w={np.array2string(np.array(W), precision=3)}")
    print(f"   conj c^2 = {c2:.8f}   best ratio^2 = {best_ratio2:.8f}   "
          f"ratio2/c2 = {best_ratio2 / c2:.6f}")
    return best_ratio2, c2, best_X

if __name__ == "__main__":
    np.set_printoptions(linewidth=140, precision=4, suppress=True)
    # sanity: rank-one extremal
    n = 3
    W = np.diag([1.0, 0.5, 0.1])
    X = np.zeros((n, n), complex); X[0, 1] = 1.0
    print("sanity ratio^2 for X=E12:", opnorm2(op_Y(X, W)), "expected", 1.25)
    print("sanity ratio^2 for X=E13:", opnorm2(op_Y(np.eye(n, k=2, dtype=complex), W)),
          "expected", 1.0 + 0.01)
    print()
    cases = [
        ((1.0, 0.5, 0.1), "n3 random-ish"),
        ((1.0, 0.9, 0.1), "n3 two large one small"),
        ((1.0, 0.99, 0.98), "n3 near equal"),
        ((1.0, 0.1, 0.1), "n3 one big"),
        ((1.0, 0.7, 0.5, 0.3), "n4"),
        ((1.0, 0.8, 0.6, 0.4, 0.2), "n5 spread"),
        ((1.0, 0.95, 0.9, 0.85, 0.8), "n5 near equal"),
        ((2.0, 1.0, 0.3, 0.3, 0.3, 0.3), "n6"),
    ]
    worst = 0.0
    for W, label in cases:
        r2, c2, X = run(W, label)
        worst = max(worst, r2 / c2)
    print("\nWorst ratio2/c2 over all cases:", worst)
