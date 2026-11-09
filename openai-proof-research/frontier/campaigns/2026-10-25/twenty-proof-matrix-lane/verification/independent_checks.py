#!/usr/bin/env python3
"""Finite rational diagnostics; the universal certificates are the Lean files."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def mm(a, b):
    n = len(a)
    return [[sum(a[i][k] * b[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)]


def transition(f):
    return [[Q(int(i == f[j])) for j in range(len(f))] for i in range(len(f))]


def rank(a):
    a = [list(row) for row in a]
    n, pivot = len(a), 0
    for c in range(n):
        r = next((r for r in range(pivot, n) if a[r][c]), None)
        if r is None:
            continue
        a[pivot], a[r] = a[r], a[pivot]
        factor = a[pivot][c]
        a[pivot] = [x / factor for x in a[pivot]]
        for r in range(n):
            if r != pivot:
                factor = a[r][c]
                a[r] = [x - factor * y for x, y in zip(a[r], a[pivot])]
        pivot += 1
    return pivot


def main():
    a = [[Q(x) for x in row] for row in ((5, 5, 5), (1, 5, 7), (7, 5, 1))]
    assert [sum(x*x for x in row) for row in a] == [75]*3
    assert [sum(a[i][j]**2 for i in range(3)) for j in range(3)] == [75]*3
    for epsilon in (Q(1, 1000), Q(1), Q(7, 2), Q(100)):
        b = [[epsilon*x for x in row] for row in a]
        means = [sum(row)/3 for row in b]
        assert all(abs(means[0]-x) < epsilon for x in b[0])
        assert abs(means[1]-b[1][0]) == 10*epsilon/3 > epsilon
    broken = [row[:] for row in a]
    broken[2][2] += 1
    assert len(set(sum(x*x for x in row) for row in broken)) > 1
    count = 0
    for n in range(1, 5):
        for f in product(range(n), repeat=n):
            t = transition(f)
            assert rank(t) == len(set(f))
            assert (rank(t) < n) == (len(set(f)) < n)
            power = [[Q(int(i == j)) for j in range(n)] for i in range(n)]
            iterate = tuple(range(n))
            seen = {}
            for k in range(n**n+1):
                assert power == transition(iterate)
                key = tuple(tuple(row) for row in power)
                if key in seen:
                    assert seen[key] < k
                    break
                seen[key] = k
                power = mm(t, power)
                iterate = tuple(f[i] for i in iterate)
            else:
                raise AssertionError('finite powers failed to repeat')
            count += 1
    result = {'status': 'PASS', 'scaled_discrepancy_cases': 4,
              'balanced_matrix_mutation_rejected': True,
              'function_matrices_checked': count, 'maximum_dimension': 4,
              'scope': 'finite rational diagnostics, not a universal proof'}
    (HERE/'independent-checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
