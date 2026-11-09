"""Exact W009 review evidence, not a factoring candidate or parameter search.

Only stdlib polynomial identities and the supplied F_7 law are checked.
Run from the factoring-research root; writes only the owned evidence JSON.
"""

from fractions import Fraction
from itertools import permutations
from pathlib import Path
import json


NAMES = ("a", "t", "z", "r", "y", "w", "U", "V", "R", "S")
ZERO = (0,) * len(NAMES)


class Poly:
    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {ZERO: terms}
        self.terms = {k: v for k, v in (terms or {}).items() if v}

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Poly) else Poly(other)

    def __add__(self, other):
        terms = self.terms.copy()
        for k, v in self.coerce(other).terms.items():
            terms[k] = terms.get(k, 0) + v
        return Poly(terms)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        terms = {}
        for k, v in self.terms.items():
            for l, w in self.coerce(other).terms.items():
                key = tuple(x + y for x, y in zip(k, l))
                terms[key] = terms.get(key, 0) + v * w
        return Poly(terms)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result


variables = []
for i in range(len(NAMES)):
    exponent = list(ZERO)
    exponent[i] = 1
    variables.append(Poly({tuple(exponent): 1}))
a, t, z, r, y, w, U, V, R, S = variables
checks = []


def identity(name, left, right):
    difference = Poly.coerce(left) - right
    assert not difference.terms, name
    checks.append({"identity": name, "zero_polynomial": True})


delta = 1 + a * t
M = [[Poly(-1), a], [t, Poly(1)]]
for i in range(2):
    for j in range(2):
        identity(f"M_squared_{i}{j}", sum(M[i][k] * M[k][j] for k in range(2)),
                 delta if i == j else 0)
identity("determinant", M[0][0] * M[1][1] - M[0][1] * M[1][0], -delta)
identity("acquired_delta_cleared", y * w + a * (a - y - w), (a - y) * (a - w))
identity("acquired_y_maps_to_w_cleared", y * w * (a - y), w * (y * w + y * (a - y - w)))
identity("acquired_w_maps_to_y_cleared", y * w * (a - w), y * (y * w + w * (a - y - w)))
identity("finite_difference_numerator", z * (z - a) * (1 + t * r) - r * (r - a) * (1 + t * z),
         (z - r) * (z + r + t * z * r - a))
identity("acquired_incidence_cleared", y * w * (z + r - a) + z * r * (a - y - w),
         a * (z * r - y * w) + y * w * (z + r) - z * r * (y + w))
A, B = U * (U - a * V), V * (V + t * U)
AR, BR = R * (R - a * S), S * (S + t * R)
identity("projective_fiber_factorization", A * BR - AR * B,
         (U * S - R * V) * (U * S + R * V + t * U * R - a * V * S))
IU, IV = a * V - U, t * U + V
identity("F_iota_numerator", IU * (IU - a * IV), delta * A)
identity("F_iota_denominator", IV * (IV + t * IU), delta * B)
identity("multiplicative_conjugacy_cleared", ((a - z) - a * (1 + t * z)) * (z - a),
         delta * z * (a - z))
identity("fixed_point_discriminant", 4 + 4 * a * t, 4 * delta)

# Arbitrary three symbolic support masses, not sampled parameter values.
weights = (a, y, w)
s = sum(weights)
v = sum(x ** 2 for x in weights)
u = sum(x ** 3 for x in weights)
q4 = sum(x ** 4 for x in weights)
q5 = sum(x ** 5 for x in weights)
legal = list(permutations(weights))
identity("three_support_legal_mass", sum(x * b * c for x, b, c in legal), s ** 3 - 3 * s * v + 2 * u)
identity("three_support_G0", sum(x ** 2 * b * c for x, b, c in legal), (s ** 2 - v) * v - 2 * s * u + 2 * q4)
identity("three_support_H0", sum(x ** 3 * b * c for x, b, c in legal), (s ** 2 - v) * u - 2 * s * q4 + 2 * q5)
identity("three_support_forced_mass", 2 * sum(x * b ** 2 * c ** 2 for x, b, c in legal),
         2 * s * (v ** 2 - q4) - 4 * v * u + 4 * q5)
identity("three_support_conditional_drift_times_three", sum(2 * b * c - x ** 2 for x, b, c in legal),
         2 * (s ** 2 - 2 * v))


# The ONLY finite-field distribution checked is the one supplied in the task.
p = 7
INF = "infinity"
points = list(range(p)) + [INF]
mu = {point: Fraction(0) for point in points}
mu.update({1: Fraction(5, 7), 2: Fraction(1, 7), 3: Fraction(1, 7)})
support = (1, 2, 3)
v_before = sum(mu[x] ** 2 for x in range(1, p))
rows = []
ell = drift_mass = zero_mass = infinity_mass = positive = removal_zero = removal_infinity = Fraction(0)
acquisition = {}


def projective(u, v):
    u %= p
    v %= p
    assert u or v, "basepoint"
    return (u * pow(v, -1, p)) % p if v else INF


for anchor, yval, wval in permutations(support):
    parameter = ((anchor - yval - wval) * pow(yval * wval, -1, p)) % p
    determinant_scale = (1 + anchor * parameter) % p
    assert determinant_scale

    def involution(point):
        U, V = (1, 0) if point == INF else (point, 1)
        return projective(anchor * V - U, V + parameter * U)

    def fold(point):
        U, V = (1, 0) if point == INF else (point, 1)
        return projective(U * (U - anchor * V), V * (V + parameter * U))

    pole = involution(INF)
    assert pole == INF or pole not in {0, anchor, yval, wval}
    assert involution(0) == anchor and involution(anchor) == 0
    assert involution(yval) == wval and involution(wval) == yval
    for point in points:
        assert involution(involution(point)) == point
        assert fold(involution(point)) == fold(point)
    pi = sum((mu[x] * mu[involution(x)] for x in range(1, p)
              if involution(x) in range(1, p) and involution(x) != x), Fraction(0))
    rho = {x: (mu[(anchor * pow(1 - x, -1, p)) % p] if x != 1 else Fraction(0))
           for x in range(1, p)}
    pi_coordinate = sum((rho[x] * rho[b] for x in range(1, p) for b in range(1, p)
                         if x != b and x * b % p == determinant_scale), Fraction(0))
    assert pi == pi_coordinate and mu[pole] == rho[determinant_scale]
    out = {point: Fraction(0) for point in points}
    for point in points:
        out[fold(point)] += mu[point]
    v_after = sum(out[x] ** 2 for x in range(1, p))
    drift = v_after - v_before
    assert drift == pi - mu[anchor] ** 2 - mu[pole] ** 2
    assert pi == 2 * mu[yval] * mu[wval]
    weight = mu[anchor] * mu[yval] * mu[wval]
    ell += weight
    drift_mass += weight * drift
    zero_mass += weight * (out[0] - mu[0])
    infinity_mass += weight * (out[INF] - mu[INF])
    positive += weight * pi
    removal_zero += weight * mu[anchor] ** 2
    removal_infinity += weight * mu[pole] ** 2
    acquisition[(anchor, parameter)] = acquisition.get((anchor, parameter), Fraction(0)) + weight
    rows.append({"a": anchor, "y": yval, "w": wval, "t": parameter,
                 "delta": determinant_scale, "b": pole, "triple_mass": str(weight),
                 "Pi": str(pi), "drift": str(drift), "v_after": str(v_after),
                 "fixed_points": [x for x in points if involution(x) == x],
                 "pushforward": {str(x): str(value) for x, value in out.items() if value}})

assert ell == Fraction(30, 343)
assert drift_mass / ell == Fraction(-5, 147)
assert zero_mass / ell == Fraction(1, 3)
assert infinity_mass == 0
assert drift_mass == positive - removal_zero - removal_infinity == Fraction(-50, 16807)
for (anchor, parameter), weight in acquisition.items():
    representative = next(row for row in rows if row["a"] == anchor and row["t"] == parameter)
    assert weight == mu[anchor] * Fraction(representative["Pi"]) == Fraction(10, 343)

result = {
    "scope": "Exact integer polynomial identities and the stated F_7 distribution only; no candidate runs, reachability tests, or prime/parameter sweeps.",
    "symbolic_checks": checks,
    "symbolic_limit": "General-law moment formulas are proved combinatorially in the report; the symbolic moment expansion here has three abstract masses.",
    "F7": {"input": {str(x): str(mu[x]) for x in support}, "ordered_legal_triples": rows,
           "legal_mass": str(ell), "conditional_drift": str(drift_mass / ell),
           "conditional_zero_increment": str(zero_mass / ell),
           "unnormalized_drift": str(drift_mass), "unnormalized_zero_increment": str(zero_mass),
           "unnormalized_infinity_increment": str(infinity_mass),
           "positive_numerator": str(positive), "zero_square_removal": str(removal_zero),
           "infinity_square_removal": str(removal_infinity),
           "acquired_maps": [{"a": key[0], "t": key[1], "mass": str(weight), "conditional_mass": str(weight / ell)}
                             for key, weight in sorted(acquisition.items())]},
    "passed": True,
}
destination = Path("research/findings/W009-pinned-review-check.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"passed": True, "symbolic_identities": len(checks), "F7_legal_triples": len(rows),
                  "F7_legal_mass": str(ell), "F7_conditional_drift": str(drift_mass / ell),
                  "output": str(destination)}))
