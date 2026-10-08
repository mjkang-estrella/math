"""Finite Fourier checks for the two rotation findings (standard library only).

These tests catch normalization/sign/duality errors. They do not establish
irrationality exponents, infinite-series convergence, or asymptotic rates.
Run from any directory: python path/to/rotation_quadrature.py
"""
import cmath
import json
import math


def phase(k, x):
    return cmath.exp(2j * math.pi * k * x)


def evaluate(coeffs, x):
    return sum(c * phase(k, x) for k, c in coeffs.items())


def main():
    alpha = 1 / math.pi
    modes = [k for k in range(-24, 25) if k]
    f = {k: complex(math.cos(k), math.sin(k)) / (1 + k * k) for k in modes}
    d = {k: cmath.exp(2j * k) - 1 for k in modes}
    u = {k: f[k] / d[k] for k in modes}
    max_residual = 0.0
    max_telescoping_error = 0.0
    max_duality_error = 0.0
    cases = 0
    for x in [0.0, 0.123, 0.75]:
        residual = evaluate(u, x + alpha) - evaluate(u, x) - evaluate(f, x)
        max_residual = max(max_residual, abs(residual))
        for n in [1, 2, 7, 19, 101]:
            direct = sum(evaluate(f, x + j * alpha) for j in range(n))
            telescoped = evaluate(u, x + n * alpha) - evaluate(u, x)
            max_telescoping_error = max(max_telescoping_error, abs(direct - telescoped))
            for s in [0.75, 1.0, 1.25, 2.0]:
                # a[k] is the value of the unnormalized error functional on e_k.
                a = {k: phase(k, x) * (cmath.exp(2j * k * n) - 1) / d[k] for k in modes}
                dual_squared = sum(abs(a[k]) ** 2 / (1 + k * k) ** s for k in modes)
                dual = math.sqrt(dual_squared)
                # Riesz extremizer, with H^s norm exactly 1 and real values.
                g = {k: a[k].conjugate() / ((1 + k * k) ** s * dual) for k in modes}
                norm_squared = sum((1 + k * k) ** s * abs(g[k]) ** 2 for k in modes)
                achieved = sum(evaluate(g, x + j * alpha) for j in range(n))
                assert abs(norm_squared - 1) < 1e-12
                assert all(abs(g[-k] - g[k].conjugate()) < 1e-12 for k in modes)
                max_duality_error = max(max_duality_error, abs(achieved - dual))
                # Finite version of the proposed 2*sqrt(S_s) bound.
                partial_s = sum((1 + k * k) ** (-s) / abs(d[k]) ** 2 for k in modes)
                assert dual_squared <= 4 * partial_s * (1 + 1e-12)
                cases += 1
    assert max_residual < 1e-10
    assert max_telescoping_error < 1e-9
    assert max_duality_error < 1e-9
    print(json.dumps({
        "status": "passed", "finite_duality_cases": cases,
        "max_coboundary_residual": max_residual,
        "max_telescoping_error": max_telescoping_error,
        "max_duality_error": max_duality_error,
        "scope": "finite Fourier normalization and duality only; not an asymptotic proof",
    }, indent=2))


if __name__ == "__main__":
    main()
