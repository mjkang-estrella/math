#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Floating-point exploration of product multipliers for Salem Bernoulli
convolutions.  EVIDENCE ONLY: double precision, no interval arithmetic.

For a Salem number beta with unit-circle angles theta_r and a multiplier
A = prod_h (beta^{k_h} - beta^{-k_h}) we compute

  Delta = sum_r |prod_h 2 sin(k_h theta_r)|      (circle conjugates)
  L     = log(1/Delta)
  Lambda = sum_{j<=0} f(A beta^j) + sum_{j>=1} f(A' beta^{-j}),
           f(u) = -log|cos(pi u)|,  A' = (-1)^m A,

using the reduction beta^n = -beta^{-n} - sum_r 2 cos(n theta_r) (mod 1) for
n >= 0, so that every phase is a signed sum of bounded terms.
"""
import cmath
import itertools
import json
import math
import sys


def real_roots_cubic_like(coeffs, lo, hi, steps=20000):
    """Bisection roots of the polynomial with integer coefficients (highest
    degree first) on [lo, hi]."""
    def p(x):
        s = 0.0
        for c in coeffs:
            s = s * x + c
        return s
    roots = []
    xs = [lo + (hi - lo) * i / steps for i in range(steps + 1)]
    for a, b in zip(xs, xs[1:]):
        pa, pb = p(a), p(b)
        if pa == 0.0:
            roots.append(a)
        elif pa * pb < 0:
            for _ in range(200):
                m = 0.5 * (a + b)
                if p(a) * p(m) <= 0:
                    b = m
                else:
                    a = m
            roots.append(0.5 * (a + b))
    return roots


class Salem:
    """Salem number from the trace polynomial T(y) with x^d T(x+1/x) = P(x)."""

    def __init__(self, trace_poly, name):
        self.name = name
        ys = real_roots_cubic_like(trace_poly, -2.5, 3.0)
        big = [y for y in ys if y > 2]
        small = [y for y in ys if -2 < y < 2]
        assert len(big) == 1 and len(small) == len(trace_poly) - 2, ys
        y0 = big[0]
        self.beta = (y0 + math.sqrt(y0 * y0 - 4)) / 2
        self.thetas = [math.acos(y / 2) for y in small]
        self.lb = math.log(self.beta)

    def g(self, n):
        """Representative of beta^n modulo 1 (exact identity mod Z)."""
        if n < 0:
            return self.beta ** n
        return -(self.beta ** (-n)) - sum(2 * math.cos(n * t) for t in self.thetas)


def f(u):
    c = abs(math.cos(math.pi * u))
    if c == 0.0:
        return float("inf")
    return -math.log(c)


def circle_values(S, ks):
    vals = []
    for t in S.thetas:
        v = 1.0
        for k in ks:
            v *= 2 * math.sin(k * t)
        vals.append(abs(v))
    return vals


def action(S, ks, tail=80):
    m = len(ks)
    b = sum(ks)
    patterns = []
    for eps in itertools.product((1, -1), repeat=m):
        sgn = 1
        for e in eps:
            sgn *= e
        patterns.append((sgn, sum(e * k for e, k in zip(eps, ks))))
    left = 0.0
    gmin = 1.0
    for j in range(-(b + tail), 1):
        u = 0.0
        for sgn, shift in patterns:
            u += sgn * S.g(j + shift)
        fu = f(u)
        left += fu
        if j <= -1:
            gmin = min(gmin, abs(math.cos(math.pi * u)))
    # A' beta^{-j} = (-1)^m A beta^{-j}; f is even, so right side mirrors left.
    right = left - f(sum(sgn * S.g(shift) for sgn, shift in patterns))
    return left + right, gmin


def best_k(S, lo, hi):
    """k in [lo, hi] minimising max_r |2 sin(k theta_r)|."""
    best = None
    for k in range(lo, hi + 1):
        v = max(abs(2 * math.sin(k * t)) for t in S.thetas)
        if best is None or v < best[0]:
            best = (v, k)
    return best


def greedy_chain(S, steps, first_hi, factor=1.0, cap=200000):
    """Greedy product: each new k in [2b+10, N] with N ~ factor*Delta^-2."""
    ks = []
    out = []
    lo, hi = 1, first_hi
    for _ in range(steps):
        if hi > cap:
            break
        v, k = best_k(S, lo, hi)
        ks.append(k)
        vals = circle_values(S, ks)
        delta = sum(vals)
        lam, gmin = action(S, ks)
        L = -math.log(delta)
        out.append({"ks": list(ks), "Delta": delta, "L": L, "Lambda": lam,
                    "ratio": lam / L if L > 0 else None, "gamma": gmin})
        b = sum(ks)
        lo = 2 * b + 10
        hi = max(lo + 10, int(factor / (delta * delta)))
    return out


def main():
    salems = {
        "quartic_P1": Salem([1, -1, -3], "x^4-x^3-x^2-x+1"),
        "sextic_P6": Salem([1, 0, -4, -1], "x^6-x^4-x^3-x^2+1"),
    }
    report = {}
    for key, S in salems.items():
        report[key] = {"beta": S.beta, "thetas": S.thetas,
                       "chain": greedy_chain(S, 6, 400)}
    json.dump(report, sys.stdout, indent=1)


if __name__ == "__main__":
    main()
