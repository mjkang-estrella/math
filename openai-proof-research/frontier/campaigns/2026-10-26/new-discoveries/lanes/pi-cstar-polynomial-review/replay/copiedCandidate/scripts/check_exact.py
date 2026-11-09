#!/usr/bin/env python3
"""Standard-library rational check of the literal six source expressions.

The sampled derivative identities are checks only; Lean proves the identity
for every complex matrix, independently of this script.
"""
from fractions import Fraction as F
import json
import random


def matrix(rows):
    return tuple(tuple(F(x) for x in row) for row in rows)


Z = matrix([[0, 0], [0, 0]])
I = matrix([[1, 0], [0, 1]])


def add(*xs):
    return tuple(tuple(sum((a[i][j] for a in xs), F(0))
                       for j in range(2)) for i in range(2))


def scale(c, a):
    return tuple(tuple(c * x for x in row) for row in a)


def sub(a, b):
    return add(a, scale(-1, b))


def mul(*xs):
    r = I
    for a in xs:
        r = tuple(tuple(sum((r[i][k] * a[k][j] for k in range(2)), F(0))
                        for j in range(2)) for i in range(2))
    return r


def star(a):
    return tuple(tuple(a[j][i] for j in range(2)) for i in range(2))


def square(a):
    return mul(a, a)


def moment(xs, p, reverse=False):
    return add(*(square(mul(star(a), a) if reverse else mul(a, star(a)))
                 if p == 2 else (mul(star(a), a) if reverse else mul(a, star(a)))
                 for a in xs))


def quadratic(a, v):
    return sum((v[i] * a[i][j] * v[j]
                for i in range(2) for j in range(2)), F(0))


def main():
    a = matrix([[1, 2], [0, -1]])
    roots = [a, scale(-2, a), a]
    critical = [I, scale(-1, I)]
    assert square(a) == I and add(*roots) == Z
    s = add(*roots)
    correction = sub(add(*(square(x) for x in roots)), scale(F(1, 9), square(s)))
    defects = []
    for kind in range(3):
        for reverse in [False, True]:
            m1, m2 = moment(roots, 1, reverse), moment(roots, 2, reverse)
            if kind == 0:
                rhs = add(scale(F(1, 9), mul(star(s), s) if reverse else mul(s, star(s))),
                          scale(F(1, 3), m1))
                lhs = moment(critical, 1, reverse)
            elif kind == 1:
                rhs = sub(scale(F(2, 9), square(m1)), scale(F(1, 3), m2))
                lhs = moment(critical, 2, reverse)
            else:
                shifted = [add(x, scale(F(1, 3), s)) for x in roots]
                shifted_products = add(*(mul(star(x), star(y), y, x) if reverse
                                         else mul(x, y, star(y), star(x))
                                         for x, y in zip(roots, shifted)))
                final_products = add(*(mul(star(x), star(s), s, x) if reverse
                                       else mul(x, s, star(s), star(x)) for x in roots))
                rhs = sub(add(scale(-1, m2), scale(F(1, 9), square(m1)),
                              scale(F(1, 9), mul(star(correction), correction) if reverse
                                    else mul(correction, star(correction))),
                              scale(F(2, 3), shifted_products)),
                          scale(F(4, 27), final_products))
                lhs = moment(critical, 2, reverse)
            defects.append(sub(rhs, lhs))
    expected = [matrix(rows) for rows in [
        [[8, -4], [-4, 0]], [[0, 4], [4, 8]],
        [[56, -24], [-24, 8]], [[8, 24], [24, 56]],
        [[-392, 168], [168, -56]], [[-56, -168], [-168, -392]]]]
    assert defects == expected
    vectors = [[1, 2], [2, -1], [1, 2], [2, -1], [1, 0], [0, 1]]
    forms = [quadratic(d, v) for d, v in zip(defects, vectors)]
    assert forms == [-8, -8, -8, -8, -392, -392]
    assert all(star(d) == d for d in defects)
    rng = random.Random(355008)
    for _ in range(100):
        z = matrix([[rng.randint(-10, 10) for _ in range(2)] for _ in range(2)])
        terms = [sub(z, x) for x in roots]
        derivative = add(mul(terms[1], terms[2]), mul(terms[0], terms[2]),
                         mul(terms[0], terms[1]))
        assert derivative == scale(3, mul(sub(z, critical[0]), sub(z, critical[1])))
    result = {"status": "PASS", "arithmetic": "fractions.Fraction, exact",
              "defects": [[[str(x) for x in row] for row in d] for d in defects],
              "vectors": vectors, "quadratic_forms": list(map(str, forms)),
              "sampled_noncommutative_argument_checks": 100,
              "universal_derivative_proof": "Lean; sampled checks alone do not prove it",
              "discovery_count_credit": 0}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
