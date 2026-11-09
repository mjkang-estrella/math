"""Fixed, preregistered exact identities only; no search or timing experiment."""
from fractions import Fraction as F
from functools import reduce
from pathlib import Path
import hashlib
import json
import sys


# Sparse polynomials in X,m,h; coefficients are exact rationals.
def add(a, b):
    c = a.copy()
    for key, value in b.items():
        c[key] = c.get(key, F(0)) + value
    return {key: value for key, value in c.items() if value}


def scale(a, scalar):
    return {key: scalar * value for key, value in a.items() if scalar * value}


def mul(a, b):
    c = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(x + y for x, y in zip(ka, kb))
            c[key] = c.get(key, F(0)) + va * vb
    return {key: value for key, value in c.items() if value}


one = {(0, 0, 0): F(1)}
X, m, h = ({(1, 0, 0): F(1)}, {(0, 1, 0): F(1)}, {(0, 0, 1): F(1)})


def prod(polys):
    return reduce(mul, polys, one)


def power(poly, k):
    return prod([poly] * k)


def total(polys):
    return reduce(add, polys, {})


def eval_h(poly, z):
    assert all(key[:2] == (0, 0) for key in poly)
    return sum(value * z ** key[2] for key, value in poly.items())


checks = []


def check(name, actual, expected):
    passed = actual == expected
    checks.append({"name": name, "passed": passed,
                   "actual": str(actual), "expected": str(expected)})


taylor_numerator = total(scale(mul(power(X, 4-j), power(h, j)), (-1)**j)
                         for j in range(5))
check("degree_four_taylor_cleared_identity",
      add(mul(add(X, h), taylor_numerator), scale(power(X, 5), -1)), power(h, 5))

denominators = [add(X, scale(m, j)) for j in range(5)]
D = prod(denominators)
newton_numerator = total(scale(mul(prod(add(h, scale(m, -j)) for j in range(k)),
                                   prod(denominators[k+1:])), (-1)**k)
                         for k in range(5))
falling5 = prod(add(h, scale(m, -j)) for j in range(5))
check("five_node_newton_cleared_identity", mul(add(X, h), newton_numerator),
      add(D, falling5))
alpha_numerator = {(a, b, 0): v for (a, b, c), v in newton_numerator.items() if c == 2}
check("quadratic_coefficient_numerator", alpha_numerator,
      total([power(X, 2), scale(mul(X, m), 10), scale(power(m, 2), 35)]))

basis = []
for j in range(5):
    numerator = prod(add(h, scale(one, -k)) for k in range(5) if k != j)
    denominator = reduce(lambda a, b: a * b, (j-k for k in range(5) if k != j), 1)
    basis.append(scale(numerator, F(1, denominator)))
check("lagrange_nodal_matrix", [[eval_h(p, z) for z in range(5)] for p in basis],
      [[F(j == z) for z in range(5)] for j in range(5)])
weights = [p.get((0, 0, 2), F(0)) for p in basis]
check("lagrange_quadratic_weights", weights,
      [F(35,24), F(-13,3), F(19,4), F(-7,3), F(11,24)])
check("lagrange_absolute_sum", sum(abs(w) for w in weights), F(40,3))

# Fixed examples of excluded hypotheses, not instances of the obstruction.
check("zero_polynomial_mod_5_roots", [x for x in range(5) if 0 % 5 == 0],
      [0,1,2,3,4])
check("composite_modulus_h_squared_roots", [x for x in range(16) if x*x % 16 == 0],
      [0,4,8,12])
integer_valued = scale(mul(h, add(h, scale(one, -1))), F(1,2))
check("integer_valued_binomial_fixed_nodes", [eval_h(integer_valued,z) for z in range(5)],
      [F(0),F(0),F(1),F(3),F(6)])
check("integer_valued_is_not_integer_coefficient", integer_valued[(0,0,2)], F(1,2))

result = {
    "preregistration_sha256": hashlib.sha256(Path(__file__).with_name("preregistration.md").read_bytes()).hexdigest(),
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    "arithmetic": "Python standard-library integers and fractions; symbolic identities",
    "checks": checks,
    "passed": sum(c["passed"] for c in checks),
    "failed": sum(not c["passed"] for c in checks),
    "performance_experiments": 0,
    "parameter_searches": 0,
}
print(json.dumps(result, indent=2))
sys.exit(1 if result["failed"] else 0)
