#!/usr/bin/env python3
"""MIT. Exact finite formula diagnostics; not a proof or a projection solver.

For small trees compare resistance formulas with independent Gram-system
solutions for the selected face projections. Larger trees check the two
families of column bounds on chosen weights, not all weights or all faces.
Writes only JSON to stdout. No dependencies beyond Python's standard library.
"""
from fractions import Fraction as Q
import json
import random


def path(e):
    out = []
    while e:
        out.append(e)
        e //= 2
    return out


def solve(matrix, rhs):
    n = len(rhs)
    a = [list(map(Q, row)) + [Q(v)] for row, v in zip(matrix, rhs)]
    for j in range(n):
        k = next(k for k in range(j, n) if a[k][j])
        a[j], a[k] = a[k], a[j]
        pivot = a[j][j]
        a[j] = [v / pivot for v in a[j]]
        for i in range(n):
            if i != j:
                c = a[i][j]
                a[i] = [x - c*y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def face_column(weights, vertices, input_edge):
    # Independent normal equations (B^T D B)c = B^T D 1_e.
    cols = [set(path(v)) for v in vertices]
    gram = [[sum((weights[k] for k in p & q), Q(0))
             for q in cols] for p in cols]
    rhs = [weights[input_edge] if input_edge in p else Q(0) for p in cols]
    c = solve(gram, rhs)
    return {k: sum((v for p, v in zip(cols, c) if k in p), Q(0))
            for k in weights}


def check(h, name, weights):
    n = 2**(h+1)-1
    resistance = {}
    subtree = {}
    for e in range(n, 0, -1):
        a = e.bit_length()-1
        if 2*e > n:
            resistance[e] = weights[e]
        else:
            r, s = resistance[2*e], resistance[2*e+1]
            resistance[e] = weights[e] + r*s/(r+s)
        subtree[e] = (h-a+1)*weights[e]/resistance[e]
    rays = {}
    for v in range(2**h, n+1):
        pp = path(v)
        rays[v] = (h+1)*max(weights[e] for e in pp)/sum(weights[e] for e in pp)
    bound = max(*subtree.values(), *rays.values())
    harmonic = sum((Q(1, j) for j in range(1, h+2)), Q(0))
    theoretical_squared = Q(h+1)/(2*harmonic)
    assert bound**2 >= theoretical_squared
    assert all(weights[e] <= 2*max(weights.values())*bound/(h-e.bit_length()+2)
               for e in weights)
    checks = 0
    if h <= 3:
        for e in range(1, n+1):
            leaves = [v for v in range(2**h, n+1) if e in path(v)]
            vertices = leaves + ([e//2] if e > 1 else [])
            y = face_column(weights, vertices, e)
            assert sum(map(abs, y.values())) == subtree[e]
            assert y[e] == weights[e]/resistance[e]
            assert all(val == 0 for k, val in y.items() if e not in path(k))
            assert all(val >= 0 for val in y.values())
            checks += 1
        for v in range(2**h, n+1):
            pp = path(v)
            e = max(pp, key=lambda k: weights[k])
            y = face_column(weights, [v], e)
            assert sum(map(abs, y.values())) == rays[v]
            checks += 1
    return {'depth': h, 'profile': name, 'edges': n,
            'selected_face_column_lower_bound': str(bound),
            'theoretical_squared_lower_bound': str(theoretical_squared),
            'independent_gram_columns_checked': checks}


def main():
    rng = random.Random(332)
    rows = []
    for h in range(9):
        edges = range(1, 2**(h+1))
        profiles = {
            'uniform': {e: Q(1) for e in edges},
            'depth_increasing': {e: Q(2**(e.bit_length()-1)) for e in edges},
            'depth_decreasing': {e: Q(1, 2**(e.bit_length()-1)) for e in edges},
            'asymmetric_integers': {e: Q(rng.randint(1, 37)) for e in edges},
            'asymmetric_rationals': {e: Q(rng.randint(1, 31), rng.randint(1, 29))
                                     for e in edges},
        }
        for name, weights in profiles.items():
            rows.append(check(h, name, weights))
    print(json.dumps({'status': 'PASS_FINITE_FORMULA_DIAGNOSTICS_ONLY',
                      'cases': rows, 'all_weights_or_depths_tested': False,
                      'full_projection_lipschitz_constant_computed': False},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
