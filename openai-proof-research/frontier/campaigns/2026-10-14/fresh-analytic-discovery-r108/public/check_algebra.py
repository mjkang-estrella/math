#!/usr/bin/env python3
"""MIT. Exact diagnostic only; does not prove T273NC108 or test Fock space."""
from fractions import Fraction as F
import json


def transpose(a):
    return [list(x) for x in zip(*a)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(2))
             for j in range(2)] for i in range(2)]


def diag(a, b):
    return [[F(a), F(0)], [F(0), F(b)]]


def box(x):
    return (F(x), F(x))


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def times(a, b):
    c = [x * y for x in a for y in b]
    return min(c), max(c)


def exp_interval(x):
    # Nonnegative Taylor series. Ratios beyond the next term are <= x/122.
    term = F(1)
    total = term
    for n in range(1, 121):
        term *= F(x, n)
        total += term
    tail = term * F(x, 121) / (1 - F(x, 122))
    den = 10**12
    lo = (total * den).__floor__()
    hi = ((total + tail) * den).__ceil__()
    return F(lo, den), F(hi, den)


def occupancy(x):
    a, b = exp_interval(x)
    return 1 / (b - 1), 1 / (a - 1)


def congruence(k, diagonal):
    return [[add(times(box(k[i][0] * k[j][0]), diagonal[0]),
                 times(box(k[i][1] * k[j][1]), diagonal[1]))
             for j in range(2)] for i in range(2)]


def slack(q, x, factor=F(1), shift=F(0)):
    return [[add(q[i] if i == j else box(0),
                 add(box(shift if i == j else 0),
                     neg(times(box(factor), x[i][j]))))
             for j in range(2)] for i in range(2)]


def positive_certificate(a):
    determinant = add(times(a[0][0], a[1][1]), neg(times(a[0][1], a[1][0])))
    assert a[0][0][0] > 0 and determinant[0] > 0
    return {"first_diagonal_lower": str(a[0][0][0]),
            "determinant_lower": str(determinant[0]),
            "approximate_lower_values": [float(a[0][0][0]), float(determinant[0])]}


def main():
    k = [[F(3, 25), F(-12, 25)], [F(2, 25), F(9, 50)]]
    u = [[F(3, 5), F(-4, 5)], [F(4, 5), F(3, 5)]]
    lam = F(1, 25)
    assert mul(transpose(u), u) == diag(1, 1)
    assert mul(mul(transpose(k), diag(1, 4)), k) == diag(lam, 9 * lam)
    # H0^(1/2) K H1^(-1/2) / sqrt(lambda), all rational here.
    normalized = mul(mul(diag(1, 2), k), diag(5, F(5, 3)))
    assert normalized == u
    frobenius_squared = sum(x*x for row in k for x in row)
    assert frobenius_squared < 1
    assert k[0][0] * k[1][1] - k[0][1] * k[1][0] != 0
    r = [occupancy(1), occupancy(9)]
    q = [occupancy(1), occupancy(4)]
    krk = congruence(k, r)
    b = slack(q, krk)
    eps = F(1, 100)
    certificates = {"B_positive": positive_certificate(b),
                    "occupation_slack": positive_certificate(slack(q, krk, 1+eps)),
                    "creation_slack": positive_certificate(slack(
                        q, congruence(k, [add(x, box(1)) for x in r]), 1+eps, 1))}
    assert b[0][1][1] < 0
    kk = mul(k, transpose(k))
    assert kk[0][1] != 0 and q[0][0] > q[1][1]
    naive_norm_squared = sum(k[j][1]**2 for j in range(2)) / lam
    assert naive_norm_squared == F(657, 100) and naive_norm_squared > 1
    print(json.dumps({"status": "EXACT_FINITE_DIAGNOSTICS_ONLY",
                      "meaning": "Checks a noncommuting stationary reference, not global Gaussian minimality or the full theorem.",
                      "K": [[str(x) for x in row] for row in k],
                      "H0": [1, 4], "H1": [1, 9], "lambda": str(lam),
                      "epsilon": str(eps), "frobenius_squared": str(frobenius_squared),
                      "polar_unitarity_and_KKT": True,
                      "KKstar_and_Q_do_not_commute": True,
                      "naive_normalization_e2_norm_squared": str(naive_norm_squared),
                      "certificates": certificates,
                      "limits": "No numerical search, no formal proof of the analytic theorem, no contribution gate."},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
