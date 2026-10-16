#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT licensed; see RIGHTS.md.
"""Exact supporting checks only. No files or network are written/accessed."""
import itertools
import json
import random
from fractions import Fraction as F


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(r) for r in zip(*a)]


def mul(a, b):
    bt = transpose(b)
    return [[sum(x*y for x, y in zip(row, col)) for col in bt] for row in a]


def det(a):
    a = [row[:] for row in a]
    z = F(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return F(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            z = -z
        v = a[j][j]
        z *= v
        for i in range(j+1, len(a)):
            t = a[i][j]/v
            for k in range(j+1, len(a)):
                a[i][k] -= t*a[j][k]
            a[i][j] = 0
    return z


def predictor(n, c):
    return [[(1-c)*c**(i-1-j) if i > j else F(0)
             for j in range(n)] for i in range(n)]


def forward_correct(signs, c):
    x = []
    for i, e in enumerate(signs):
        x.append(e + (1-c)*sum(c**(i-1-j)*x[j] for j in range(i)))
    return x


def discrepancy_sq(vectors, order, signs):
    s = [0]*len(vectors[0])
    ans = 0
    for i in order:
        s = [a + signs[i]*b for a, b in zip(s, vectors[i])]
        ans = max(ans, sum(a*a for a in s))
    return ans


def minimax(vectors, orders):
    # Negating all signs preserves squared norms, so fix the first sign.
    best = None
    witness = None
    for tail in itertools.product((-1, 1), repeat=len(vectors)-1):
        signs = (1,) + tail
        val = max(discrepancy_sq(vectors, order, signs) for order in orders)
        if best is None or val < best:
            best, witness = val, signs
    assert best == max(discrepancy_sq(vectors, o, witness) for o in orders)
    return best, list(witness)


def main():
    congruences = 0
    crossed = 0
    spectra = 0
    for c in (F(0), F(1, 2), F(3, 5), F(4, 5), F(15, 17)):
        for n in range(1, 19):
            k = [[F(0) if i == j else
                  (c**(i-j-1) if i > j else -c**(j-i-1))
                  for j in range(n)] for i in range(n)]
            l = eye(n)
            for i in range(1, n):
                l[i][i-1] = -c
            jmat = [[F(i == j+1)-F(j == i+1) for j in range(n)] for i in range(n)]
            assert mul(mul(l, k), transpose(l)) == jmat
            assert det(k) == F(n % 2 == 0)
            congruences += 1
        for m in range(1, 17):
            n = 2*m
            pred = predictor(n, c)
            transform = [[F(i == j)-pred[i][j] for j in range(n)] for i in range(n)]
            extracted = [[sum(transform[2*l][2*j] for l in range(k+1))
                          for j in range(m)] for k in range(m)]
            claimed = [[(1+c**(2*(k-j)+1))/(1+c) if k >= j else F(0)
                        for j in range(m)] for k in range(m)]
            assert extracted == claimed
            crossed += 1
    for n in range(1, 19):
        t = [[F(i >= j) for j in range(n)] for i in range(n)]
        diff = eye(n)
        for i in range(1, n):
            diff[i][i-1] = -1
        assert mul(t, diff) == eye(n) == mul(diff, t)
        g = mul(transpose(diff), diff)
        expected = [[F(2 if i == j and i < n-1 else 1 if i == j else
                       -1 if abs(i-j) == 1 else 0) for j in range(n)] for i in range(n)]
        assert g == expected
        # Characteristic polynomial recurrence verified by exact evaluations.
        # Both sides have degree n; n+1 values prove polynomial equality.
        for lam in range(n+1):
            a, b = F(1), F(1-lam)
            for _ in range(2, n+1):
                a, b = b, (2-lam)*b-a
            mat = [[g[i][j]-F(lam if i == j else 0) for j in range(n)] for i in range(n)]
            assert det(mat) == b
        spectra += 1
    incompatible = []
    c = F(4, 5)
    for n in (2, 4, 6, 8):
        pred = predictor(n, c)
        count = 0
        for signs in itertools.product((-1, 1), repeat=n):
            x = forward_correct(signs, c)
            reverse_signs = [x[i]-sum(pred[j][i]*x[j] for j in range(n))
                             for i in range(n)]
            assert reverse_signs != list(signs)
            count += 1
        incompatible.append({'n': n, 'signings_excluded': count})
    explicit = []
    for m in range(1, 65):
        n = 2*m
        signs = tuple(e for j in range(m) for e in ((-1)**j, -(-1)**j))
        oddsfirst = list(range(0, n, 2))+list(range(1, n, 2))
        assert discrepancy_sq([(1,)]*n, range(n), signs) == 1
        assert discrepancy_sq([(1,)]*n, oddsfirst, signs) == 1
        explicit.append(m)
    rng = random.Random(2026101604)
    palette = [(5, 0), (0, 5), (3, 4), (-3, 4), (3, -4), (4, 3), (0, 0)]
    finite = []
    for n in (4, 6, 8, 10, 12):
        for trial in range(5):
            vectors = [rng.choice(palette) for _ in range(n)]
            order = list(range(n))
            rng.shuffle(order)
            val, witness = minimax(vectors, [list(range(n)), order])
            finite.append({'n': n, 'trial': trial, 'vectors_times_5': vectors,
                           'second_order_zero_based': order,
                           'minimax_squared': str(F(val, 25)), 'signs': witness})
    # Mutation controls: correct matrices must not pass as transposed or shifted.
    k = [[F(0), -F(1)], [F(1), F(0)]]
    l = [[F(1), F(0)], [-F(1, 2), F(1)]]
    assert mul(mul(l, transpose(k)), transpose(l)) != k
    pred = predictor(6, F(4, 5))
    wrong = [[F(i == j)-pred[j][i] for j in range(6)] for i in range(6)]
    wrong_b = [[sum(wrong[2*l][2*j] for l in range(k+1)) for j in range(3)] for k in range(3)]
    correct_b = [[(1+F(4, 5)**(2*(k-j)+1))/(1+F(4, 5)) if k >= j else F(0)
                  for j in range(3)] for k in range(3)]
    assert wrong_b != correct_b
    print(json.dumps({'status': 'PASS_support_only',
                      'congruence_and_determinant_cases': congruences,
                      'crossed_submatrix_cases': crossed,
                      'inverse_gram_characteristic_cases': spectra,
                      'feedback_sign_checks': incompatible,
                      'explicit_easy_two_order_controls': len(explicit),
                      'mutation_controls': 2,
                      'finite_minimax_instances': finite}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
