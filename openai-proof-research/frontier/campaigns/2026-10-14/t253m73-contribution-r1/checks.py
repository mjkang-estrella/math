#!/usr/bin/env python3
"""MIT. Standard-library symbolic/finite checks; not a proof of the theorem."""
import itertools as it
import json


def constant(x):
    return {(0, 0): x} if x else {}


def add(*polys):
    out = {}
    for poly in polys:
        for k, v in poly.items():
            out[k] = out.get(k, 0)+v
    return {k: v for k, v in out.items() if v}


def scale(poly, n):
    return {k: n*v for k, v in poly.items() if n*v}


def mul(a, b):
    out = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            out[i+k, j+l] = out.get((i+k, j+l), 0)+x*y
    return {k: v for k, v in out.items() if v}


def det(matrix):
    out = {}
    n = len(matrix)
    for perm in it.permutations(range(n)):
        sign = (-1)**sum(perm[i] > perm[j] for i in range(n) for j in range(i+1, n))
        term = constant(sign)
        for i, j in enumerate(perm):
            term = mul(term, matrix[i][j])
        out = add(out, term)
    return out


def smith_integer(matrix):
    """Euclidean unimodular row/column operations, independent of minors."""
    a = [row[:] for row in matrix]
    rows, cols = len(a), len(a[0])
    for k in range(min(rows, cols)):
        places = [(abs(a[i][j]), i, j) for i in range(k, rows)
                  for j in range(k, cols) if a[i][j]]
        if not places:
            break
        _, i, j = min(places)
        a[k], a[i] = a[i], a[k]
        for row in a:
            row[k], row[j] = row[j], row[k]
        while True:
            restart = False
            for i in range(k+1, rows):
                if a[i][k]:
                    q = a[i][k]//a[k][k]
                    a[i] = [x-q*y for x, y in zip(a[i], a[k])]
                    if a[i][k]:
                        a[k], a[i] = a[i], a[k]
                    restart = True
                    break
            if restart:
                continue
            for j in range(k+1, cols):
                if a[k][j]:
                    q = a[k][j]//a[k][k]
                    for row in a:
                        row[j] -= q*row[k]
                    if a[k][j]:
                        for row in a:
                            row[k], row[j] = row[j], row[k]
                    restart = True
                    break
            if restart:
                continue
            bad = next(((i, j) for i in range(k+1, rows) for j in range(k+1, cols)
                        if a[i][j] % a[k][k]), None)
            if bad is None:
                break
            i, _ = bad
            a[k] = [x+y for x, y in zip(a[k], a[i])]
        if a[k][k] < 0:
            a[k] = [-x for x in a[k]]
    diagonal = [a[i][i] for i in range(min(rows, cols))]
    assert all(a[i][j] == 0 for i in range(rows) for j in range(cols) if i != j)
    return diagonal


def run():
    u, v, one, zero = {(1, 0): 1}, {(0, 1): 1}, constant(1), {}
    uv = add(u, v)
    c = [v, uv, scale(u, -1), scale(v, -1)]
    h = [scale(v, -1), u, scale(uv, -1), v]
    minors = [det([[c[i], h[i]], [c[j], h[j]]]) for i, j in it.combinations(range(4), 2)]
    divisor = mul(v, add(scale(u, 2), v))
    assert minors == [divisor, scale(divisor, -1), zero, scale(divisor, -1), divisor, scale(divisor, -1)]
    def wedge(x, y):
        return [add(mul(x[i], y[j]), scale(mul(x[j], y[i]), -1))
                for i, j in it.combinations(range(4), 2)]
    basis = [[one if i == j else zero for i in range(4)] for j in range(4)]
    pairs = [(basis[0], basis[1]), (basis[2], basis[3]),
             ([one, zero, u, v], [zero, one, v, uv]),
             ([u, v, one, zero], [v, uv, zero, one])]
    columns = [wedge(x, y) for x, y in pairs]
    assert columns[2][1:5] == c and columns[3][1:5] == h
    arrangement = [[scale(u, -1), scale(v, -1), one, zero],
                   [scale(v, -1), scale(uv, -1), zero, one],
                   [one, zero, scale(u, -1), scale(v, -1)],
                   [zero, one, scale(v, -1), scale(uv, -1)]]
    determinant = det(arrangement)
    norm_lambda = add(mul(u, u), mul(u, v), scale(mul(v, v), -1))
    trace = add(scale(u, 2), v)
    expected_det = add(mul(add(norm_lambda, one), add(norm_lambda, one)), scale(mul(trace, trace), -1))
    assert determinant == expected_det
    def evaluate(poly, x, y):
        return sum(coef*x**i*y**j for (i, j), coef in poly.items())
    fib = [0, 1]
    for _ in range(100):
        fib.append(fib[-1]+fib[-2])
    samples = []
    for a in range(1, 49):
        x, y = fib[a-1], fib[a]
        b = [[evaluate(columns[j][i], x, y) for j in range(4)] for i in range(6)]
        diagonal = smith_integer(b)
        d = fib[2*a]
        assert diagonal == [1, 1, 1, d]
        m = abs(evaluate(determinant, x, y))
        assert m == (2*x+y)**2-2*(-1)**a-2
        assert (d % 2 == 0) == (a % 3 == 0)
        assert a % 3 != 0 or d % 8 == 0
        if a <= 6:
            samples.append({'a': a, 'M': m, 'd': d, 'smith_diagonal': diagonal})
    doubling = {str(d): (d//2) % 2 for d in (2, 4, 6, 8, 10, 12)}
    assert doubling == {'2': 1, '4': 0, '6': 1, '8': 0, '10': 1, '12': 0}
    return {'status': 'PASS_BOUNDED_DIAGNOSTICS', 'dependencies': 'Python standard library',
            'symbolic_minor_signs': [1, -1, 0, -1, 1, -1],
            'symbolic_arrangement_identity': 'det(B_integer)=(Norm(lambda)+1)^2-Trace(lambda)^2',
            'smith_parameter_values': 48, 'samples': samples, 'cyclic_doubling_controls': doubling,
            'limits': 'No source-admissibility assertion for small a; no proof of exactness, coherence, primitive lift, transfer, or the infinite theorem.',
            'campaign_credit': 0}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
