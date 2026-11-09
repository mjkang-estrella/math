#!/usr/bin/env python3
"""Exact algebra only. No finite-field walks, parameter sampling, or candidate runs.

Sparse multivariate polynomials over Q verify universal numerator identities.
The accompanying report supplies induction and probability proofs for all depths.
Uses only the Python standard library; writes only this review's output prefix.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json


class Poly:
    n = 4  # a, T, b, u

    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.c = dict(value.c)
        elif isinstance(value, dict):
            self.c = {e: Q(v) for e, v in value.items() if v}
        else:
            self.c = {(0,) * self.n: Q(value)} if value else {}

    @classmethod
    def var(cls, i):
        e = [0] * cls.n
        e[i] = 1
        return cls({tuple(e): 1})

    def __add__(self, other):
        out = dict(self.c)
        for e, c in Poly(other).c.items():
            out[e] = out.get(e, Q(0)) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({e: -c for e, c in self.c.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        out = {}
        for e, c in self.c.items():
            for f, d in Poly(other).c.items():
                ef = tuple(x + y for x, y in zip(e, f))
                out[ef] = out.get(ef, Q(0)) + c * d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result

    def diff(self, i):
        out = {}
        for e, c in self.c.items():
            if e[i]:
                f = list(e)
                f[i] -= 1
                out[tuple(f)] = c * e[i]
        return Poly(out)

    def subst(self, i, value):
        value = Poly(value)
        result = Poly()
        for e, c in self.c.items():
            f = list(e)
            f[i] = 0
            result += Poly({tuple(f): c}) * value ** e[i]
        return result


checks = []


def check(label, left, right=0):
    residual = Poly(left) - right
    assert not residual.c, (label, residual.c)
    checks.append({'name': label, 'zero_residual': True})


a, t, b, u = (Poly.var(i) for i in range(4))
D = 2 * a * (a + 1) ** 2
C = (3 * t - t ** 3) * Q(1, 2)
F = C + b * t * (1 - t ** 2) ** 2
num = D * C + (a + 2) * t * (1 - t ** 2) ** 2
qa = (a + 2) * t ** 2 + (a + 2) ** 2 * t + 2 * (a + 1) ** 2
R = 3 * a ** 2 + 9 * a + 8
S = a ** 2 + 3 * a + 1

check('target_minus_one_factorization', num - D, (t - 1) ** 2 * (t - a) * qa)
check('odd_map', num.subst(1, -t), -num)
check('target_plus_one_factorization', num + D,
      (t + 1) ** 2 * (t + a) * qa.subst(1, -t))
check('chosen_anchor', num.subst(1, a), D)
check('opposite_anchor', num.subst(1, -a), -D)
check('zero_fixed', num.subst(1, 0))
check('one_fixed', num.subst(1, 1), D)
check('minus_one_fixed', num.subst(1, -1), -D)
check('critical_one', num.diff(1).subst(1, 1))
check('critical_minus_one', num.diff(1).subst(1, -1))
check('a_minus_two_degree_drop', num.subst(0, -2), -4 * C)
check('a_minus_two_Q_constant', qa.subst(0, -2), 2)
check('quadratic_discriminant', (a + 2) ** 4 - 8 * (a + 2) * (a + 1) ** 2,
      a * (a + 2) * (a ** 2 - 2 * a - 4))
check('Q_at_one', qa.subst(1, 1), R)
check('Q_at_anchor', qa.subst(1, a), 2 * (a + 1) * S)
check('Q_at_minus_one', qa.subst(1, -1), a * (a + 1))
check('Q_prime_at_one', qa.diff(1).subst(1, 1), (a + 2) * (a + 4))
check('Q_prime_at_anchor', qa.diff(1).subst(1, a), (a + 2) * (3 * a + 2))
check('collision_conditions_separated_outside_5', R - 3 * S, 5)
check('no_double_Q_root_at_one_outside_2_5', R - (a + 4) * (3 * a - 3), 20)
check('no_double_Q_root_at_anchor_outside_3_5', 9 * S - (3 * a + 2) * (3 * a + 7), -5)
check('critical_factorization', F.diff(1), (t ** 2 - 1) * (5 * b * t ** 2 - b - Q(3, 2)))
check('fixed_point_factorization', F - t, t * (t ** 2 - 1) * (b * t ** 2 - b - Q(1, 2)))

# Fresh-flat equation after clearing the displayed chart denominator.
hit_plus = 2 * b * t * (t + 1) ** 2 - (t + 2)
check('flat_hazard_numerator', 2 * (F - 1), (t - 1) ** 2 * hit_plus)

# Cubic normalization, symmetry, and base recurrence for the all-depth proof.
g = 3 * t ** 2 - 2 * t ** 3
check('affine_conjugacy_C_to_g', (C.subst(1, 2 * t - 1) + 1) * Q(1, 2), g)
check('g_reflection', g.subst(1, 1 - t), 1 - g)
check('g_base_factorization', g, t ** 2 * (3 - 2 * t))
check('g_critical_derivative', g.diff(1), 6 * t * (1 - t))
check('g_three_halves_to_zero', g.subst(1, Q(3, 2)))
check('g_zero_fixed', g.subst(1, 0))
check('g_one_fixed', g.subst(1, 1), 1)
check('one_anchor_normalization', ((a * t) ** 3 - 3 * a ** 2 * (a * t)), -2 * a ** 3 * C)

# Probability algebra, variables a,t now stand for local target masses.
check('endpoint_disjoint_events', a * (1 - t) + t * (1 - a) + Q(1, 2) * a * t,
      a + t - Q(3, 2) * a * t)
check('endpoint_lower_bound_decomposition', a + t - Q(3, 2) * a * t,
      a * (1 - t * Q(1, 2)) + t * (1 - a))
check('union_first_hit_telescoping_step',
      (1 - (1 - a - b) * (1 - t - u)) - (1 - (1 - a) * (1 - t)),
      b * (1 - t) + u * (1 - a) - b * u)

# A known critically fixed quintic specialization: this is symbolic, not a search.
smooth5 = 10 * t ** 3 - 15 * t ** 4 + 6 * t ** 5
check('b_three_eighths_known_quintic',
      (F.subst(2, Q(3, 8)).subst(1, 2 * t - 1) + 1) * Q(1, 2), smooth5)
check('b_three_eighths_parameter_equation', 3 * a * (a + 1) ** 2 - 4 * (a + 2), (a - 1) * R)

# An exact characteristic-zero non-PCF witness, using a 3-adic valuation
# argument in the report. No critical orbit is numerically iterated.
check('a_two_b_one_ninth', num.subst(0, 2), 36 * F.subst(2, Q(1, 9)))
check('a_two_free_critical_value', F.subst(2, Q(1, 9)) - Q(203, 450) * t,
      t * (t ** 2 - Q(29, 10)) * (t ** 2 * Q(1, 9) - Q(2, 5)))

# Characteristic-five degeneracy is excluded by the actual chart.
five_identity = (a + 2 - 2 * a * (a + 1) ** 2) + 2 * (a - 1) ** 3
assert all(c.denominator == 1 and c.numerator % 5 == 0 for c in five_identity.c.values())
checks.append({'name': 'characteristic_5_b_minus_one_is_negative_anchor_cube_over_unit',
               'zero_residual_mod_5': True})

output = Path(__file__).with_name('W011-two-color-review-certificate-output.json')
result = {
    'scope': 'Exact symbolic polynomial identities only; no candidate evaluation, basin census, random sampling, or parameter search.',
    'arithmetic': 'Python standard library fractions.Fraction; sparse polynomials over Q',
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'checks': checks,
    'all_passed': True,
    'count': len(checks),
    'not_machine_proved': ['All-depth induction, Chebotarev application, multiplicity case exhaustion, and full stochastic process proofs are in the review report.'],
}
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'all_passed': True, 'checks': len(checks), 'output': str(output)}))
