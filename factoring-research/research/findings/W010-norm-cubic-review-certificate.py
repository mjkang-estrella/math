#!/usr/bin/env python3
"""Exact identities only: no candidate run, field enumeration, or search."""

import json
from fractions import Fraction as F


# Sparse integer polynomials in eight indeterminates. No external CAS.
NAMES = ("T", "z", "u", "p", "epsilon", "h", "t", "H")
ZERO_EXP = (0,) * len(NAMES)


class Poly:
    def __init__(self, terms):
        self.terms = {e: c for e, c in terms.items() if c}

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly({ZERO_EXP: value})

    def __add__(self, other):
        result = dict(self.terms)
        for e, c in self.coerce(other).terms.items():
            result[e] = result.get(e, 0) + c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        result = {}
        for e, c in self.terms.items():
            for f, d in self.coerce(other).terms.items():
                g = tuple(a + b for a, b in zip(e, f))
                result[g] = result.get(g, 0) + c * d
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, power):
        assert isinstance(power, int) and power >= 0
        result = self.coerce(1)
        for _ in range(power):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms


def variable(name):
    exponent = tuple(int(n == name) for n in NAMES)
    return Poly({exponent: 1})


T, z, u, p, epsilon, h, t, H = map(variable, NAMES)
checks = []


def check(name, predicate):
    if not predicate:
        raise AssertionError(name)
    checks.append(name)


Q = z**2 + z*u + u**2
check("cubic factorization over Z[T,z,u]",
      (T-z)*(T-u)*(T+z+u) == T**3-Q*T+z*u*(z+u))
check("sampled cubic image", z**3-Q*z == -z*u*(z+u))
check("third cubic image", (-z-u)**3-Q*(-z-u) == -z*u*(z+u))
check("completed square", 4*Q == (2*z+u)**2+3*u**2)

C, D = p-epsilon-4, 3+h
check("total legal conic count",
      (p-1)*(1+epsilon)+(p-1)*C == (p-1)*(p-3))
sum_k_squared = (p-1)**2*(1+epsilon)**2+(p-1)*(C**2+D**2)
sum_k_a_scaled = (p-1)*(C-D)
target_numerator = (p-1)*(1+epsilon)**2+C**2+D**2-C+D
check("uniform conditional residual numerator",
      sum_k_squared-sum_k_a_scaled == (p-1)*target_numerator)

# Six prespecified sign/interchange orbits; these cover the symbolic support.
anchors = ((3, 5), (3, -5), (3, 7), (3, -7), (5, 7), (5, -7))
parameters = tuple(a*a+a*b+b*b for a, b in anchors)
check("predetermined orbit parameters", parameters == (49, 19, 79, 37, 109, 39))
check("no integer parameter coincidence", len(set(parameters)) == 6)
check("only occupied root overlap", set(parameters) & {9, 25, 49} == {49})
check("support certificate valid without modular wrap for p>109",
      all(0 < b <= 109 for b in parameters))
check("pointwise selected images", 3**3-49*3 == 5**3-49*5 == -120)
check("selected root image", 7**3-49*7 == 0)
check("raw weighted drift polynomial",
      2*(4*t**2)**2+4*(4*t*H)**2-(4*t**2)*(2*H**2)
      == 32*t**4+56*t**2*H**2)
v_poly, q4_poly = 4*t**2+2*H**2, 4*t**4+2*H**4
check("forced energy of this support (R=0)",
      4*(v_poly**2-2*q4_poly) == 2*(4*t**2)**2+4*(4*t*H)**2)

small, heavy = F(1, 12), F(1, 4)
m = 1-4*small-2*heavy
s = 1-m
v = 4*small**2+2*heavy**2
ell = s*s-2*v
delta = 4*small**2-2*heavy**2
raw_drift = 32*small**4+56*small**2*heavy**2
check("fixed masses normalized", m == F(1, 6))
check("fixed legal probability", ell == F(7, 18))
check("fixed initial residual mass", v == F(11, 72))
check("fixed bad-parameter probability", 4*small**2/ell == F(1, 14))
check("negative pointwise drift", delta == F(-7, 72))
check("fixed remaining residual mass", v+delta == F(1, 18))
check("positive raw expected drift", raw_drift == F(67, 2592))
check("positive conditional expected drift", raw_drift/ell == F(67, 1008))

print(json.dumps({
    "kind": "exact_algebraic_certificate",
    "scope": "displayed polynomial identities and one prespecified symbolic support",
    "numerical_candidate_runs": 0,
    "prime_or_weight_searches": 0,
    "finite_field_enumerations": 0,
    "general_drift_inequality": "proved in the accompanying report, not by these checks",
    "checks_passed": len(checks),
    "checks": checks,
    "fixed_witness": {
        "field_condition": "any prime p > 109",
        "small_mass": str(small), "heavy_mass": str(heavy), "zero_mass": str(m),
        "ell": str(ell), "initial_v": str(v),
        "pointwise_delta_v_at_beta_49": str(delta),
        "raw_expected_delta_v": str(raw_drift),
        "conditional_expected_delta_v": str(raw_drift/ell),
        "reachability_claimed": False,
    },
}, indent=2))
