#!/usr/bin/env python3
"""Independent exact-arithmetic checks; standard library only.

This is a diagnostic companion to, not a replacement for, the Lean proof.
"""
from fractions import Fraction
import json


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matmul(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def matvec(a, v):
    return [sum(x * y for x, y in zip(row, v)) for row in a]


def rank(a):
    a = [[Fraction(x) for x in row] for row in a]
    k = 0
    for j in range(len(a[0])):
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        pivot = a[k][j]
        a[k] = [x / pivot for x in a[k]]
        for i in range(len(a)):
            if i != k:
                factor = a[i][j]
                a[i] = [x - factor * y for x, y in zip(a[i], a[k])]
        k += 1
    return k


def det(a):
    a = [[Fraction(x) for x in row] for row in a]
    ans = Fraction(1)
    for k in range(len(a)):
        p = next((i for i in range(k, len(a)) if a[i][k]), None)
        if p is None:
            return Fraction(0)
        if p != k:
            a[k], a[p] = a[p], a[k]
            ans = -ans
        pivot = a[k][k]
        ans *= pivot
        for i in range(k + 1, len(a)):
            factor = a[i][k] / pivot
            a[i] = [x - factor * y for x, y in zip(a[i], a[k])]
    return ans


def main():
    m = [[4, 4, 1], [2, 2, 5], [3, 3, 3]]
    x = [1, 0, -1]
    y = [3, -3, 0]
    assert matvec(m, x) == y
    assert y != [0] * 3
    assert matvec(m, y) == [0] * 3
    assert all(entry > 0 for row in m for entry in row)
    assert list(map(sum, m)) == [9] * 3
    assert list(map(sum, zip(*m))) == [9] * 3
    assert rank(m) == 2 and rank(matmul(m, m)) == 1
    # Characteristic polynomial lambda^2 (lambda - 9), checked at four
    # distinct rational points; both polynomials have degree three.
    for lam in [-2, 0, 1, 3]:
        assert det([[lam * int(i == j) - m[i][j] for j in range(3)]
                    for i in range(3)]) == lam * lam * (lam - 9)

    # The exact change of basis and all displayed three-dimensional variants.
    p = [[1, 1, 1], [1, -1, 1], [1, 0, -2]]
    assert det(p) == 6
    shift_cases = [Fraction(0), Fraction(1), Fraction(1, 2), Fraction(7, 3)]
    for t in shift_cases:
        a = [[m[i][j] + t * int(i == j) for j in range(3)] for i in range(3)]
        jordan = [[t + 9, 0, 0], [0, t, 6], [0, 0, t]]
        assert matmul(a, p) == matmul(p, jordan)
        assert det(a) == (t + 9) * t * t
        b = [[entry / (t + 9) for entry in row] for row in a]
        assert list(map(sum, b)) == [1] * 3
        assert list(map(sum, zip(*b))) == [1] * 3
        assert min(min(row) for row in b) > 0
        shifted = [[b[i][j] - t / (t + 9) * int(i == j)
                    for j in range(3)] for i in range(3)]
        assert matvec(shifted, x) == [z / (t + 9) for z in y]
        assert matvec(shifted, y) == [0] * 3
    b0 = [[Fraction(entry, 9) for entry in row] for row in m]
    assert matmul(b0, b0) == [[Fraction(1, 3)] * 3 for _ in range(3)]

    # A stronger family of nonsingular counterexamples in all dimensions >=3.
    cases = 0
    for n in range(3, 9):
        u = [1, -1, 0] + [0] * (n - 3)
        v = [1, 1, -2] + [0] * (n - 3)
        nn = [[a * b for b in v] for a in u]
        assert matmul(nn, nn) == [[0] * n for _ in range(n)]
        for c in range(3, 8):
            a = [[int(i == j) + c + nn[i][j] for j in range(n)]
                 for i in range(n)]
            b = [[a[i][j] - int(i == j) for j in range(n)]
                 for i in range(n)]
            assert min(min(row) for row in a) > 0
            assert list(map(sum, a)) == [1 + c * n] * n
            assert list(map(sum, zip(*a))) == [1 + c * n] * n
            assert matvec(b, v) == [6 * t for t in u]
            assert matvec(b, u) == [0] * n
            assert rank(b) == 2 and rank(matmul(b, b)) == 1
            assert det(a) == 1 + c * n
            cases += 1
    print(json.dumps({"status": "PASS", "arithmetic": "exact rational",
                      "main_matrix": m, "rank_M": 2, "rank_M_squared": 1,
                      "characteristic_polynomial": "lambda^2*(lambda-9)",
                      "shifted_stochastic_cases": len(shift_cases),
                      "Jordan_basis_determinant": 6,
                      "additional_family_cases": cases}, indent=2))


if __name__ == "__main__":
    main()
