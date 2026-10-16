#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT.

Exact finite controls for candidate.md; no floating-point decisions.
Default invocation compares with the frozen receipt and writes nothing.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]


class I:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = F(lo), F(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = as_i(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -as_i(other)

    def __rsub__(self, other):
        return as_i(other) + -self

    def __mul__(self, other):
        other = as_i(other)
        v = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return I(min(v), max(v))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = as_i(other)
        assert other.lo * other.hi > 0
        return self * I(1 / other.hi, 1 / other.lo)

    def receipt(self):
        d = 1 << 80
        lower = (self.lo.numerator * d) // self.lo.denominator
        upper = -((-self.hi.numerator * d) // self.hi.denominator)
        assert F(lower, d) <= self.lo <= self.hi <= F(upper, d)
        return {"dyadic_denominator": str(d), "lower_numerator": str(lower),
                "upper_numerator": str(upper),
                "decimal_orientation_only": [float(self.lo), float(self.hi)]}


def as_i(x):
    return x if isinstance(x, I) else I(x)


@lru_cache(None)
def log_unit(x):
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    n = 100
    s = 2*sum((z**(2*j+1)/F(2*j+1) for j in range(n)), F(0))
    tail = 2*z**(2*n+1)/((2*n+1)*(1-z*z))
    return I(s, s+tail)


@lru_cache(None)
def log_q(x):
    x = F(x)
    assert x > 0
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x > 2:
        x /= 2
        k += 1
    return log_unit(x) + k*log_unit(F(2))


def g(x):
    x = F(x)
    assert x >= 0
    return (x+1)*log_q(x+1) - x*log_q(x) if x else I(0)


def h(x):
    assert x > 0
    return log_q(1+1/x)


def transpose(a):
    return [list(row) for row in zip(*a)]


def matmul(a, b):
    return [[sum((x*y for x, y in zip(row, col)), F(0))
             for col in zip(*b)] for row in a]


def scale(s, a):
    return [[s*x for x in row] for row in a]


def add(a, b):
    return [[x+y for x, y in zip(r, s)] for r, s in zip(a, b)]


def det(a):
    a = [list(row) for row in a]
    result = F(1)
    for j in range(len(a)):
        i = next((i for i in range(j, len(a)) if a[i][j]), None)
        if i is None:
            return F(0)
        if i != j:
            a[i], a[j] = a[j], a[i]
            result *= -1
        pivot = a[j][j]
        result *= pivot
        for i in range(j+1, len(a)):
            q = a[i][j]/pivot
            for k in range(j+1, len(a)):
                a[i][k] -= q*a[j][k]
    return result


def fock_output(k, ell):
    total = k+ell
    p = []
    for m in range(total+1):
        coeff = sum(comb(k, i)*comb(ell, m-i)*(-1)**(k-i)
                    for i in range(max(0, m-ell), min(k, m)+1))
        p.append(F(coeff*coeff*factorial(m)*factorial(total-m),
                   factorial(k)*factorial(ell)*2**total))
    assert sum(p) == 1
    assert sum(m*q for m, q in enumerate(p)) == F(total, 2)
    return p


def calculate():
    a, b = F(1, 10), F(1)
    c = (a+b)/2
    p, q = h(c)/(2*h(a)), h(c)/(2*h(b))
    deficit_weight = 1-p-q
    kappa = g(c)-p*g(a)-q*g(b)
    assert deficit_weight.lo > 0
    assert kappa.hi < 0
    thermal_correlation = 2*g(c)-g(a)-g(b)
    assert thermal_correlation.lo > 0

    # A product of two purified thermal states, memory holding both purifiers.
    conditional_deficit = -deficit_weight*g(F(100))-kappa
    assert conditional_deficit.hi < 0

    # Actual equality input + thermal auxiliary at the SAME entropy levels.
    # Common one-mode squeeze diag(2,1/2) gives t=(2+1/2)/2=5/4.
    t = F(5, 4)
    aa, bb, cc = [t*(x+F(1, 2))-F(1, 2) for x in (a, b, c)]
    assert (aa, bb, cc) == (F(1, 4), F(11, 8), F(13, 16))
    plus_deficit = g(cc)-p*g(aa)-q*g(bb)-kappa
    assert plus_deficit.lo > 0

    penalties = []
    for gamma in (0, 1, 10, 100, 1000):
        u = F(1, 1024*(gamma+1))
        delta = b-a
        corr = -delta*u/(1-u*u)
        radius = delta*(1+u*u)/(1-u*u)
        upper, lower = (a+b+radius)/2, (a+b-radius)/2
        assert radius**2 == delta**2 + 4*corr**2
        assert lower > 0 and corr*corr < a*b
        mutual = g(a)+g(b)-g(upper)-g(lower)
        assert mutual.lo > 0
        loss = g(c+corr)-g(c)+gamma*mutual
        assert loss.hi < 0
        penalties.append({"gamma": gamma, "cross_covariance": str(corr),
                          "joint_photon_eigenvalues": [str(lower), str(upper)],
                          "penalized_change": loss.receipt()})

    # An internally correlated two-mode symplectic covariance, all rational.
    j = [[F(x) for x in row] for row in
         [[0,1,0,0],[-1,0,0,0],[0,0,0,1],[0,0,-1,0]]]
    squeeze = [[F(0) for _ in range(4)] for _ in range(4)]
    for i, x in enumerate((F(2), F(1,2), F(3), F(1,3))):
        squeeze[i][i] = x
    passive = [[F(x) for x in row] for row in
               [[F(3,5),0,F(4,5),0],[0,F(3,5),0,F(4,5)],
                [-F(4,5),0,F(3,5),0],[0,-F(4,5),0,F(3,5)]]]
    s = matmul(passive, squeeze)
    assert matmul(matmul(s,j),transpose(s)) == j and det(s) == 1
    shape = matmul(s,transpose(s))
    va, vb, vc = [scale(x+F(1,2),shape) for x in (a,b,c)]
    assert add(scale(F(1,2),va),scale(F(1,2),vb)) == vc
    assert shape[0][2] != 0
    assert det(va) == (a+F(1,2))**4
    assert det(vb) == (b+F(1,2))**4
    assert det(vc) == (c+F(1,2))**4
    cross = scale(F(1,2), add(vb, scale(-1,va)))
    assert any(x for row in cross for x in row)
    wrong = [[F(0) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        wrong[i][i] = b+F(1,2)
    mixed = add(scale(F(1,2),va),scale(F(1,2),wrong))
    assert det(mixed) > (c+F(1,2))**4

    fock = []
    for k in range(5):
        for ell in range(5):
            probs = fock_output(k, ell)
            entropy = -sum((r*log_q(r) for r in probs if r), I(0))
            if k+ell:
                assert entropy.lo > 0
            fock.append({"k": k, "ell": ell,
                         "probabilities": [str(x) for x in probs]})

    # A faithful diagonal state has every number moment but infinite score norm.
    score_terms = []
    for k in range(6):
        even, odd = F(1, 2**(k+1)), F(1, 2**(4**(k+1)))
        v = 4**(k+1)-k-1
        coefficient = 2*odd-even
        actual_times_Z = (1-v)*coefficient*(2*k+1)
        lower_times_Z = F(2*k+1)*F(2)**(k-1)
        assert coefficient <= -even/2
        assert actual_times_Z >= lower_times_Z
        score_terms.append({"k": k, "frequency": v,
                            "proven_lower_bound_times_Z": str(lower_times_Z)})

    return {"status": "PASS", "decisions": "rational interval/exact fraction only",
            "log_series_terms": 100,
            "reference": {"a":str(a),"b":str(b),"eta":"1/2"},
            "p":p.receipt(), "q":q.receipt(), "one_minus_p_minus_q":deficit_weight.receipt(),
            "kappa":kappa.receipt(), "thermal_output_mutual_information":thermal_correlation.receipt(),
            "purified_memory_conditional_deficit":conditional_deficit.receipt(),
            "same_level_extremal_doubling_plus_deficit":plus_deficit.receipt(),
            "finite_mutual_information_penalty_controls":penalties,
            "symplectic_covariance_controls": {"matrix_dimension":4,"determinant_shape":str(det(shape)),
                "internal_cross_entry":str(shape[0][2]),"wrong_shape_determinant":str(det(mixed)),
                "claimed_equal_shape_determinant":str((c+F(1,2))**4)},
            "fock_controls":fock, "infinite_score_lower_bounds":score_terms,
            "limitations":"Finite controls support the analytic arguments; they do not prove the unresolved Gaussianity bridge."}


if __name__ == '__main__':
    result = calculate()
    target = ROOT/'receipts/checks.json'
    if sys.argv[1:] == ['--record']:
        target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    elif sys.argv[1:]:
        raise SystemExit('usage: check.py [--record]')
    else:
        assert json.loads(target.read_text()) == result, 'frozen receipt mismatch'
    print('PASS: interval obstructions, 5 finite penalties, covariance controls, 25 Fock controls, 6 score lower bounds')
