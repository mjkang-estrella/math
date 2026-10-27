#!/usr/bin/env python3
"""Explore the literal matrix Shapiro trace inequality; numerical evidence only."""
from pathlib import Path
import json
import time
import numpy as np
from scipy.optimize import minimize


def matrices(x, p, n):
    lo = np.tril_indices(n)
    z = x.reshape(p - 1, len(lo[0]))
    L = np.zeros((p - 1, n, n))
    L[:, lo[0], lo[1]] = z
    for j in range(n):
        idx = np.flatnonzero((lo[0] == j) & (lo[1] == j))[0]
        L[:, j, j] = np.exp(z[:, idx])
    A = np.concatenate((np.eye(n)[None], L @ np.swapaxes(L, 1, 2)))
    return A, L


def objective(x, p, n):
    A, L = matrices(x, p, n)
    B = np.roll(A, -1, axis=0) + np.roll(A, -2, axis=0)
    V = np.linalg.inv(B)
    f = np.einsum('ijk,ikj->', A, V) - p * n / 2
    H = V @ A @ V
    G = V - np.roll(H, 1, axis=0) - np.roll(H, 2, axis=0)
    GL = 2 * G[1:] @ L
    for j in range(n):
        GL[:, j, j] *= L[:, j, j]
    lo = np.tril_indices(n)
    return float(f), GL[:, lo[0], lo[1]].reshape(-1)


def main():
    start = time.monotonic()
    rng = np.random.default_rng(352327)
    results = []
    hit = None
    for p, n in [(12, 2), (23, 2), (12, 3), (23, 3)]:
        lo = np.tril_indices(n)
        bounds1 = [(-5, 5) if i == j else (-20, 20) for i, j in zip(*lo)]
        bounds = bounds1 * (p - 1)
        best = float('inf')
        for trial in range(30):
            x = rng.normal(0, .7 if trial % 2 else 1.7, (p - 1) * len(lo[0]))
            out = minimize(objective, x, args=(p, n), jac=True, method='L-BFGS-B',
                           bounds=bounds, options={'maxiter': 1500, 'maxls': 50,
                                                   'ftol': 1e-13, 'gtol': 1e-8})
            f = objective(out.x, p, n)[0]
            best = min(best, f)
            if f < -1e-5:
                A, _ = matrices(out.x, p, n)
                hit = {'p': p, 'n': n, 'deficit': f, 'trial': trial,
                       'parameters': out.x.tolist(), 'matrices': A.tolist(),
                       'smallest_eigenvalue': float(np.linalg.eigvalsh(A).min())}
                break
        row = {'p': p, 'n': n, 'trials': trial + 1, 'best_deficit': best}
        results.append(row)
        print(json.dumps(row), flush=True)
        if hit:
            break
    result = {'source': '2110.10933v1 Conjecture2.9 /MathDB352327',
              'domain': 'Strictly positive definite real symmetric inputs via Cholesky, A0=I by congruence',
              'results': results, 'hit': hit, 'seconds': time.monotonic() - start,
              'qualification': 'Numerical exploration only; no proof, exact counterexample, or discovery credit.'}
    Path('search-result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'hit': hit is not None, 'seconds': result['seconds']}), flush=True)


if __name__ == '__main__':
    main()
