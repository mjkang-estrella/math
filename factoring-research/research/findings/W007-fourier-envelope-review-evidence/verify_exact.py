#!/usr/bin/env python3
"""Exact algebra supporting the W007 Fourier audit; no field/tape enumeration.

This is not a formal proof checker for Weil, orthogonality, or probability.
It checks the finite symbolic identities and rational constants cited in the
report. Only Python's standard library is used. It never runs a candidate.
"""
from fractions import Fraction as F
from math import comb
import json


class Poly:
    """Three-variable sparse polynomials over Q."""

    def __init__(self, terms=None):
        self.t = {m: F(c) for m, c in (terms or {}).items() if c}

    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly({(0, 0, 0): value})

    def __add__(self, other):
        result = self.t.copy()
        for m, c in self.lift(other).t.items():
            result[m] = result.get(m, F(0)) + c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.t.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        result = {}
        for a, c in self.t.items():
            for b, d in self.lift(other).t.items():
                m = tuple(x + y for x, y in zip(a, b))
                result[m] = result.get(m, F(0)) + c * d
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = self.lift(1)
        for _ in range(n):
            result = result * self
        return result

    def shifted_first(self, amount):
        result = Poly()
        for (a, b, c), value in self.t.items():
            for j in range(a + 1):
                result += Poly({(j, b, c): value * comb(a, j) * amount**(a-j)})
        return result

    def at_first(self, value):
        assert all(b == c == 0 for _, b, c in self.t)
        return sum((coefficient * F(value)**a for (a, _, _), coefficient in self.t.items()), F(0))


checks = []


def identity(name, left, right):
    assert not (Poly.lift(left) - right).t, name
    checks.append({"name": name, "status": "PASS", "kind": "polynomial identity over Q"})


def nonnegative(name, polynomial):
    assert all(c >= 0 for c in polynomial.t.values()), name
    checks.append({"name": name, "status": "PASS", "kind": "nonnegative coefficients on nonnegative orthant",
                   "coefficients": {str(m): str(c) for m, c in sorted(polynomial.t.items())}})


def rational(name, condition):
    assert condition, name
    checks.append({"name": name, "status": "PASS", "kind": "exact rational comparison"})


x = Poly({(1, 0, 0): 1})
y = Poly({(0, 1, 0): 1})
z = Poly({(0, 0, 1): 1})
identity("quadratic collision factorization", x*(x-z)-y*(y-z), (x-y)*(x+y-z))
# x = degree, y = sqrt(p), z = C. Clear the denominator y^6.
identity("Fourier normalization after p=sqrt(p)^2", (x-1)*y*(y*y*z-y**4), (x-1)*y**3*(z-y*y))
# x = 2^i, y = i; numerators of A_(i+1)-A_i.
identity("exponential-envelope increment", (2*x-1-(y+1))-(x-1-y), x-1)

k = x
a = k + F(1, 6)*k*(k-1)*(2*k-1)
b = k*k + 1
identity("training envelope telescopes", a.shifted_first(1)-a, b)
rational("training envelope base a(0)=0", a.at_first(0) == 0)
nonnegative("a(k)<=k^3 for k>=2", (k**3-a).shifted_first(2))
nonnegative("b(k)<=5*k^2/4 for k>=2", (F(5, 4)*k*k-b).shifted_first(2))
nonnegative("k*(k-1)/2>=k^2/4 for k>=2", (F(1, 2)*k*(k-1)-F(1, 4)*k*k).shifted_first(2))
nonnegative("a(k)/4^k decreases for k>=2", (4*a-a.shifted_first(1)).shifted_first(2))
nonnegative("b(k)/4^k decreases for k>=2", (4*b-b.shifted_first(1)).shifted_first(2))
rational("p>=1024, k<=4: A<=1/4", 2*a.at_first(4)/1024 <= F(1, 4))
rational("p>=1024, k<=4: B<=1/8", 2*b.at_first(4)/1024 <= F(1, 8))
rational("k>=5, p>=4^k: A<=1/4", 2*a.at_first(5)/4**5 <= F(1, 4))
rational("k>=5, p>=4^k: B<=1/8", 2*b.at_first(5)/4**5 <= F(1, 8))
nonnegative("floor(x)>=x-1>=x/2 for x>=2: second inequality", (k-1-F(1, 2)*k).shifted_first(2))
rational("training-work constant", F(3, 4)*F(1, 4) == F(3, 16))
rational("short-budget ratio constant", F(3, 16)/F(5, 4) == F(3, 20))
rational("long-budget ratio constant", F(1, 2)*F(1, 8)/F(5, 4) == F(1, 20))
rational("eta<=2/p conversion", F(1, 20)/2 == F(1, 40))

print(json.dumps({"scope": "Symbolic polynomial identities and rational constants only; no prime, residue, history, or candidate enumeration.",
                  "checks": checks, "count": len(checks)}, indent=2))
