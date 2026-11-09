#!/usr/bin/env python3
"""Exact rational bookkeeping of every power of mu used in analysis.md.

Conventions: mu = eps^-2, alpha = mu^-A, eps^P = mu^-(P/2).  Each entry is
(name, exponent of mu, requirement).  Pure standard library.
"""
from fractions import Fraction as Fr
import sys

A = Fr(7, 3)        # alpha = mu^{-7/3}
G = Fr(7, 3)        # GRR exponent gamma
P = 12              # accuracy power eps^P for all TV remainders (K chosen after P)
ETA = Fr(1, 20)     # H prop:cutoff
p_hold = 22         # Holder exponent in the transfer lemma

checks = [
    # GRR expectation of B for the grid interpolation (section 6)
    ("alpha^(3-gamma)            [below-cell regular term]", -A * (3 - G), "<0"),
    ("alpha^(2-gamma)/mu         [jump term]", -A * (2 - G) - 1, "<0"),
    # e = C mu^2 eps^P is the additive fourth-moment remainder of Prop. B
    ("mu^2 eps^P alpha^(1-gamma) [TV remainder in E B]", 2 - Fr(P, 2) - A * (1 - G), "<0"),
    # microscopic modulus (section 5)
    ("sqrt(mu)*alpha             [free flight in a cell]", Fr(1, 2) - A, "<0"),
    ("mu*alpha                   [mean colliders per cell]", 1 - A, "<=0"),
    ("(1/alpha)*mu*alpha/k^3     [union bound, k~sqrt(mu)]", Fr(1) - Fr(3, 2), "<0"),
    ("(1/alpha)*mu^3 eps^P/k^3   [union bound remainder]", A + 3 - Fr(P, 2) - Fr(3, 2), "<0"),
    # fourth moment remainder (section 4): mu^2 eps^P and (mu eps^P)^2
    ("mu^2 eps^P                 [kappa_4/mu^2 remainder]", 2 - Fr(P, 2), "<0"),
    # transfer (prior support): sqrt(mu) * P(E)^(1-1/p)
    ("sqrt(mu) P(E)^(1-1/p)      [exact-centering transfer]",
     Fr(1, 2) - (1 + ETA) * (1 - Fr(1, p_hold)) / 2, "<0"),
]

ok = True
for name, e, req in checks:
    good = (e < 0) if req == "<0" else (e <= 0)
    ok &= good
    print(f"{name:58s} mu^{str(e):>7s}  {req}  {'ok' if good else 'FAIL'}")

# GRR modulus: |f(t)-f(s)| <= C B^{1/4} int_0^d u^{gamma/4-3/2} du
integrand = G / 4 - Fr(3, 2)
print(f"GRR integrand exponent gamma/4-3/2 = {integrand} (> -1 needed)",
      "ok" if integrand > -1 else "FAIL")
print(f"GRR Holder exponent (gamma-2)/4 = {(G - 2) / 4}")
ok &= integrand > -1

# admissible alpha = mu^-a window: a > 1/2 (free flight), a >= 1 (mu*alpha<=1),
# a*(gamma-2) < 1 (jump term); gamma in (2,3)
lo, hi = max(Fr(1, 2), Fr(1)), 1 / (G - 2)
print(f"admissible a for gamma=7/3: [{lo}, {hi}) ; chosen a = {A}",
      "ok" if lo <= A < hi else "FAIL")
ok &= lo <= A < hi
print("PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
