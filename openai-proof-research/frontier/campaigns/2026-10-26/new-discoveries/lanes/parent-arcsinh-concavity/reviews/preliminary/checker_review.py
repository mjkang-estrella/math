#!/usr/bin/env python3
"""Independent preliminary-review checker (own derivation, no reuse of parent code).

Target: strict concavity of p -> arcsinh_p(x) = int_0^x (1+t^p)^(-1/p) dt on (0,inf),
fixed x = 1/4096. Witness midpoint p1=1/6 between p0=1/12 and p2=1/4.

Independent steps:
1. Substitution t = u^N gives F(1/N, 2^-12) = N int_0^{2^(-12/N)} u^(N-1)/(1+u)^N du.
2. Build the Taylor truncations of (1+u)^-4 (deg 3) and (1+u)^-6 (deg 6) from the
   binomial series myself; prove the defect polynomial identities by exact expansion;
   verify remainder positivity for u>=0 by rational-root-free positivity via exact
   coefficient sign check (all coefficients positive).
3. Exact rational integration with fractions.Fraction -> L, U, gap.
4. High-precision direct quadrature of F at the three p (mpmath, independent of the
   polynomial route) to confirm the defect is positive and the bounds are consistent.
"""
from fractions import Fraction as Fr
from math import comb
import sys

def F_rational_bound_check():
    # Binomial-series truncations derived independently:
    # (1+u)^-m = sum_j (-1)^j C(m+j-1, j) u^j  (converges for |u|<1; used only via
    # the exact polynomial identity, not by series convergence).
    P3 = [(-1)**j * comb(3 + j, j) for j in range(4)]      # deg 3
    P6 = [(-1)**j * comb(5 + j, j) for j in range(7)]      # deg 6
    print("P3 coeffs:", P3, "P6 coeffs:", P6)

    # exact polynomial multiplication
    def polymul(a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[i + j] += x * y
        return out

    # (1+u)^4 * P3 and (1+u)^6 * P6
    A = polymul([1, 4, 6, 4, 1], P3)
    B = polymul([1, 6, 15, 20, 15, 6, 1], P6)
    print("(1+u)^4 P3 =", A)   # expect [1,0,0,0,-35,-84,-70,-20]
    print("(1+u)^6 P6 =", B)   # expect [1,0,0,0,0,0,0,-792,-3465,-6160,-5544,-2520,-462]
    assert A == [1, 0, 0, 0, -35, -84, -70, -20], A
    assert B == [1, 0, 0, 0, 0, 0, 0, 792, 3465, 6160, 5544, 2520, 462], B
    # remainder polys have all-positive coefficients => for u>=0:
    # (1+u)^4 P3 <= 1  i.e. P3 <= (1+u)^-4 ; and (1+u)^6 P6 >= 1 i.e. P6 >= (1+u)^-6.
    # (Direction of P6 bound: (1+u)^6 P6 - 1 = +u^7*(pos) >= 0.)
    print("directions OK: P3 <= (1+u)^-4 and P6 >= (1+u)^-6 for u >= 0")

    # exact rational integrals
    def exact_int(coeffs, a, b, m):  # int_a^b u^m * P(u) du
        tot = Fr(0)
        for k, c in enumerate(coeffs):
            tot += Fr(c) * (Fr(b) ** (m + k + 1) - Fr(a) ** (m + k + 1)) / Fr(m + k + 1)
        return tot

    # x = 1/4096 = 2^-12 ; N=4: upper limit 2^-3 = 1/8 ; N=6: upper limit 2^-2 = 1/4
    L = Fr(4) * exact_int(P3, 0, Fr(1, 8), 3)
    U = Fr(6) * exact_int(P6, 0, Fr(1, 4), 5)
    print("L (lower bound for F(1/4,1/4096)) =", L, "=", float(L))
    print("U (upper bound for F(1/6,1/4096)) =", U, "=", float(U))
    gap_lower = (L - 2 * U) / 2   # >= (F(1/12)+F(1/4))/2 - F(1/6), using F(1/12)>=0
    print("midpoint defect lower bound =", gap_lower, "=", float(gap_lower))
    assert L == Fr(2291, 13762560), L
    assert U == Fr(1574453, 19377684480), U
    assert gap_lower == Fr(38411, 19377684480) > 0
    print("EXACT MATH GATE: PASS (all identities/integrals rederived from scratch)")
    return float(gap_lower)

def numeric_quadrature(gap_lb):
    import mpmath as mp
    mp.mp.dps = 60
    x = mp.mpf(1) / 4096
    def F(p):
        f = lambda t: (1 + t**p) ** (-1 / p)
        return mp.quad(f, [0, x])
    p0, p1, p2 = mp.mpf(1) / 12, mp.mpf(1) / 6, mp.mpf(1) / 4
    d = (F(p0) + F(p2)) / 2 - F(p1)
    print("F(1/12) =", F(p0))
    print("F(1/6)  =", F(p1))
    print("F(1/4)  =", F(p2))
    print("midpoint defect (60-dps quadrature) =", d)
    assert d > gap_lb > 0, (d, gap_lb)
    # cross-check against the hypergeometric closed form x*2F1(1/p,1/p;1+1/p;-x^p)
    for p in (p0, p1, p2):
        hg = x * mp.hyper([1 / p, 1 / p], [1 + 1 / p], -x**p)
        assert abs(hg - F(p)) < mp.mpf(10) ** (-45)
    print("quadrature matches hypergeometric closed form; defect > proved bound")
    print("NUMERIC SANITY: PASS (evidence only, not part of proof)")

if __name__ == "__main__":
    g = F_rational_bound_check()
    try:
        numeric_quadrature(g)
    except ImportError:
        print("mpmath unavailable; exact gate alone stands")
    print("OVERALL: PASS")
