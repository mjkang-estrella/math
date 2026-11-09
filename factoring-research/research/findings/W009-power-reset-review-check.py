#!/usr/bin/env python3
"""Exact identities for this audit; no sampling or factoring candidate execution.

Uses sparse polynomials over Z (and coefficient reduction in one fixed
characteristic) with variables X,Y,W. No third-party packages are needed.
The identities support the prose proof; they do not mechanize curve theory.
"""

from datetime import datetime, timezone
from fractions import Fraction
from math import gcd
from pathlib import Path
import json


def poly(value):
    if isinstance(value, dict):
        return {m: c for m, c in value.items() if c}
    return {} if not value else {(0, 0, 0): Fraction(value)}


def add(*terms):
    out = {}
    for term in terms:
        for m, c in poly(term).items():
            out[m] = out.get(m, 0) + c
    return poly(out)


def neg(term):
    return {m: -c for m, c in poly(term).items()}


def mul(*terms):
    out = poly(1)
    for term in terms:
        nxt = {}
        for m, c in out.items():
            for n, d in poly(term).items():
                k = tuple(a + b for a, b in zip(m, n))
                nxt[k] = nxt.get(k, 0) + c * d
        out = poly(nxt)
    return out


def power(term, exponent):
    out = poly(1)
    for _ in range(exponent):
        out = mul(out, term)
    return out


def derivative(term, variable=0):
    out = {}
    for monomial, coefficient in poly(term).items():
        if monomial[variable]:
            new = list(monomial)
            new[variable] -= 1
            out[tuple(new)] = coefficient * monomial[variable]
    return poly(out)


X, Y, W = ({(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1})
checks = []


def identity(name, lhs, rhs, formula, modulus=None):
    difference = add(lhs, neg(rhs))
    if modulus is not None:
        difference = poly({m: int(c) % modulus for m, c in difference.items()})
    assert not difference, (name, difference)
    checks.append({"name": name, "formula": formula, "modulus": modulus,
                   "residual_polynomial": [], "passed": True})


numerator = mul(add(X, neg(Y)), add(X, neg(W)))
identity("outer numerator expansion", numerator,
         add(power(X, 2), neg(mul(add(Y, W), X)), mul(Y, W)),
         "(X-Y)(X-W)=X^2-(Y+W)X+YW")
identity("fold derivative numerator", add(mul(derivative(numerator), X), neg(numerator)),
         add(power(X, 2), neg(mul(Y, W))),
         "X*N'(X)-N(X)=X^2-YW, hence F'=1-YW/X^2")

# X=D, Y=ell: multiply the ramification-budget gap by ell.
identity("four-fiber strict gap", add(mul(4, X, add(Y, -1)), neg(mul(Y, add(mul(2, X), -2)))),
         add(mul(2, X, add(Y, -2)), mul(2, Y)),
         "ell*[4D(1-1/ell)-(2D-2)]=2D(ell-2)+2ell>0 for D>=1,ell>=2")
identity("four-square boundary gap", add(mul(2, X), neg(add(mul(2, X), -2))),
         2, "4D(1-1/2)-(2D-2)=2")
identity("three-cube boundary gap", add(mul(3, X, Fraction(2, 3)), neg(add(mul(2, X), -2))),
         2, "3D(1-1/3)-(2D-2)=2")
identity("three-fiber strict gap", add(mul(3, X, add(Y, -1)), neg(mul(Y, add(mul(2, X), -2)))),
         add(mul(X, add(Y, -3)), mul(2, Y)),
         "ell*[3D(1-1/ell)-(2D-2)]=D(ell-3)+2ell>0 for D>=1,ell>=3")

# X=ell; genus arithmetic for the four tame branch points.
identity("superelliptic genus arithmetic", add(mul(-2, X), mul(4, add(X, -1))),
         add(mul(2, add(X, -1)), -2),
         "-2ell+4(ell-1)=2(ell-1)-2")

# Fixed characteristic illustration of the general Frobenius identity, not a sweep.
identity("Frobenius anchor roots in characteristic five",
         mul(add(power(X, 5), neg(power(Y, 5))), add(power(X, 5), neg(power(W, 5)))),
         power(numerator, 5),
         "(X^5-Y^5)(X^5-W^5)=((X-Y)(X-W))^5 mod 5; denominator is X^5",
         modulus=5)

# Exact divisibility-congruence certificate, with no enumeration of F_5 points.
T = add(power(X, 5), neg(X))
P = add(T, 3)
A = mul(add(P, -1), add(P, -2))
identity("finite-field coincidence certificate", add(A, neg(mul(4, P))),
         mul(T, add(T, -1)),
         "For P=X^5-X+3, (P-1)(P-2)-4P=(X^5-X)*(X^5-X-1) mod 5",
         modulus=5)
identity("coincidence example separability", derivative(P), -1,
         "(X^5-X+3)'=-1 mod 5", modulus=5)

# X=d, Y=m: character encoding respects valuation classes at every pole.
identity("pole encoding valuation congruence",
         add(mul(add(X, -1), Y), Y), mul(X, Y),
         "(d-1)m-(-m)=dm")

# Divisor arithmetic for a concrete composite exponent, over odd characteristic.
# F_(y,w)(X^2) has four simple zeros and two poles of order two.
valuations = [1, 1, 1, 1, -2, -2]
index = gcd(*valuations)
powered_index = gcd(*(6 * value for value in valuations))
assert index == 1 and powered_index == 6 and powered_index % 4 != 0
checks.append({"name": "composite-exponent divisibility",
               "formula": "gcd(1,1,1,1,-2,-2)=1; multiplying by e=6 gives index 6, not divisible by 4",
               "passed": True, "base_index": index, "powered_index": powered_index})

destination = Path(__file__).with_name("W009-power-reset-review-check.json")
result = {"generated_at_utc": datetime.now(timezone.utc).isoformat(),
          "method": "Exact sparse-polynomial and integer arithmetic; Python standard library only",
          "scope": "Proof-support identities only; no candidate execution, input sampling, prime or depth sweep",
          "checks": checks, "all_passed": all(c["passed"] for c in checks)}
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"checks": len(checks), "all_passed": result["all_passed"], "path": str(destination)}))
