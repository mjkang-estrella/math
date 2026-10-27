#!/usr/bin/env python3
"""Stable positive-form search for real2x2 SPD Shapiro inputs (numerics only)."""
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import differential_evolution, minimize


def value(x, p):
    z = np.concatenate((np.zeros((1, 3)), x.reshape(p - 1, 3)))
    scale, shape, angle = z.T
    ij = np.arange(p)
    j, k = (ij + 1) % p, (ij + 2) % p

    def cross(a, b):
        return 2 * np.exp(scale[a] + scale[b]) * (
            np.cosh(shape[a] - shape[b]) +
            2 * np.sinh(shape[a]) * np.sinh(shape[b]) * np.sin(angle[a] - angle[b]) ** 2)

    return float(np.sum((cross(ij, j) + cross(ij, k)) /
                        (np.exp(2 * scale[j]) + np.exp(2 * scale[k]) + cross(j, k))) - p)


def main():
    start = time.monotonic()
    rows, hit = [], None
    for p in [5, 6]:
        bounds = [(-6, 6), (0, 6), (-np.pi, np.pi)] * (p - 1)
        out = differential_evolution(value, bounds, args=(p,), rng=352327+p,
                                     maxiter=1200, popsize=12, tol=1e-9,
                                     polish=False, updating='immediate')
        local = minimize(value, out.x, args=(p,), method='L-BFGS-B', bounds=bounds,
                         options={'maxiter': 4000, 'ftol': 1e-14, 'gtol': 1e-8})
        best = min(float(out.fun), float(local.fun))
        rows.append({'p': p, 'n': 2, 'global_value': float(out.fun),
                     'polished_value': float(local.fun), 'evaluations': out.nfev})
        print(json.dumps(rows[-1]), flush=True)
        if best < -1e-7:
            hit = {'p': p, 'n': 2, 'deficit': best,
                   'parameters': (local.x if local.fun <= out.fun else out.x).tolist()}
            break
    result = {'source': '2110.10933v1: lower lengths5/6 propagate by Proposition2.8 to23/12',
              'parametrization': 'A_i=exp(s_i)*R(theta_i)*diag(exp(t_i),exp(-t_i))*R(theta_i)^T',
              'calculation': 'Positive Lorentz cross-products avoid inverse-matrix cancellation',
              'results': rows, 'hit': hit, 'seconds': time.monotonic() - start,
              'qualification': 'Numerical search only, no exact witness or proof or credit.'}
    Path('hyperbolic-search-result.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
