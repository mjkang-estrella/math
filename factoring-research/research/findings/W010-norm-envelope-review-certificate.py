#!/usr/bin/env python3
"""Exact symbolic identities supporting the review, using only stdlib.

No candidate execution, field enumeration, prime/weight search, random sampling,
depth sweep, numerical approximation, or empirical complexity inference.
The report supplies the general proofs and the applicability conditions.
"""

from fractions import Fraction as F
import json
from pathlib import Path


NAMES = ("x", "y", "z", "u", "w", "m", "v", "a", "j", "k", "T", "r", "s")
ZERO = (0,) * len(NAMES)


class Poly:
    def __init__(self, value=0):
        self.terms = ({e: F(c) for e, c in value.items() if c}
                      if isinstance(value, dict)
                      else ({ZERO: F(value)} if value else {}))

    @staticmethod
    def lift(value):
        return value if isinstance(value, Poly) else Poly(value)

    def __add__(self, other):
        terms = dict(self.terms)
        for e, c in self.lift(other).terms.items():
            terms[e] = terms.get(e, 0) + c
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        terms = {}
        for e1, c1 in self.terms.items():
            for e2, c2 in self.lift(other).terms.items():
                e = tuple(a + b for a, b in zip(e1, e2))
                terms[e] = terms.get(e, 0) + c1 * c2
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = Poly(1)
        for _ in range(n):
            result = result * self
        return result


def variable(name):
    exponents = list(ZERO)
    exponents[NAMES.index(name)] = 1
    return Poly({tuple(exponents): 1})


x, y, z, u, w, m, v, a, j, k, T, r, s = map(variable, NAMES)
checks = []


def identity(name, left, right):
    residual = Poly.lift(left) - right
    assert not residual.terms, (name, residual.terms)
    checks.append({"name": name, "kind": "rational_polynomial_identity", "passed": True})


def positive_coefficients(name, expression):
    assert expression.terms and all(c >= 0 for c in expression.terms.values())
    checks.append({"name": name, "kind": "nonnegative_coefficients_for_nonnegative_variables", "passed": True})


identity("cubic anchor factorization",
         (x-z)*(x-u)*(x+z+u), x**3-(z*z+z*u+u*u)*x+z*u*(z+u))
identity("leading-form simple-root certificate",
         (2*w+1)**2-4*(w*w+w+1), -3)
identity("quadratic norm completion of square",
         4*(z*z+z*u+u*u), (2*z+u)**2+3*u*u)
identity("uniform-start Parseval numerator",
         (x-1)**2+(x-1), x*(x-1))
identity("exact local anchor hazard",
         1-((1-m)**2-2*v), 2*m-m*m+2*v)
identity("parent union-bound relaxation slack",
         (4*m+2*v)-(2*m+2*(m*m+v)), 2*m*(1-m))
identity("sharpened anchor relaxation slack",
         (2*m+2*v)-(1-((1-m)**2-2*v)), m*m)

# Here x=1/p and a=81^j are formal symbols. No numerical depths are run.
Vj = (j+1)*x+F(1,5)*(a-1)*x*x
Vnext = (j+2)*x+F(1,5)*(81*a-1)*x*x
identity("geometric recurrence for V", Vnext-Vj, x+16*a*x*x)
identity("residual geometric constant", F(16,80), F(1,5))
identity("root geometric constant", F(4,8), F(1,2))
identity("root bound at j=k-1", 2*((k-1)+F(6,5)), 2*k+F(2,5))
identity("sqrt(2j+2/5)<=j+1 squared slack",
         (j+1)**2-(2*j+F(2,5)), j*j+F(3,5))
positive_coefficients("nonnegative root simplification slack", j*j+F(3,5))
identity("linear residual simplification slack",
         F(6,5)*(j+1)-(j+F(6,5)), F(1,5)*j)
positive_coefficients("nonnegative residual simplification slack", F(1,5)*j)

# Here x=m_p, y=m_q. These are probability-polynomial identities only.
identity("pin proper-factor probability",
         x*(1-y)+(1-x)*y, x+y-2*x*y)
identity("pin clean/full/proper partition",
         (1-x)*(1-y)+x*y+(x+y-2*x*y), 1)
identity("one-probe proper-factor probability",
         r*(1-s)+(1-r)*s, r+s-2*r*s)
identity("unit gate root-mass expectation for two symbolic opposite pairs",
         2*x*(m+x)+2*y*(m+y), 2*(x+y)*m+2*x*x+2*y*y)
zero_mass = 1-2*x-2*y
identity("unrestricted pin endpoint mean for two symbolic opposite pairs",
         zero_mass**2+2*x*(zero_mass+x)+2*y*(zero_mass+y),
         zero_mass+2*x*x+2*y*y)

# Here x=1/p, y=1/q, and P=X. These are symbolic in the primes.
identity("P=X unrestricted pin endpoint root mean",
         x+x*(1-x), 2*x-x*x)
identity("P=X conditioned-versus-unrestricted discrepancy",
         2*x-(2*x-x*x), x*x)
identity("P=X clean-pin proper probe law",
         (2*x)*(1-2*y)+(1-2*x)*(2*y), 2*x+2*y-8*x*y)
identity("k=0 sharpened union bound at one prime",
         (T+1)*x+T*(x-x*x), (2*T+1)*x-T*x*x)

identity("training success coefficient",
         2*(F(3,2)+F(6,5))*k*(k+1)*F(1,2), F(27,10)*k*(k+1))
identity("terminal success coefficient",
         ((T+1)*F(3,2)+T*F(6,5))*(k+1), (F(27,10)*T+F(3,2))*(k+1))
identity("combined explicit success coefficient",
         F(27,10)*k*(k+1)+(F(27,10)*T+F(3,2))*(k+1),
         (k+1)*(F(27,10)*(k+T)+F(3,2)))

result = {
    "scope": "Exact rational polynomial identities; no candidate or search execution",
    "candidate_runs": 0,
    "prime_or_weight_searches": 0,
    "depth_sweeps": 0,
    "checks_passed": len(checks),
    "checks_failed": 0,
    "checks": checks,
    "limitations": [
        "The Deligne theorem and its hypotheses are verified in the report from the original PDF.",
        "Probability identities require the independence and chart rules stated in the report.",
        "General inequalities, stopping, and Jensen arguments are mathematical proofs in the report.",
        "This certificate is not a formal proof or an empirical performance test."
    ]
}
target = Path(__file__).with_name("W010-norm-envelope-review-certificate-output.json")
target.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"checks_passed": len(checks), "checks_failed": 0, "output": target.name}))
