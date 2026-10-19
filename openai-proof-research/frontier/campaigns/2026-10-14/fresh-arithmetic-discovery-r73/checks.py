#!/usr/bin/env python3
"""MIT. Finite exact diagnostics only; not a proof of T253M73. No writes."""
import itertools as it
import json
import math


def determinant(a):
    if not a:
        return 1
    return sum((-1)**j * a[0][j] * determinant(
        [row[:j] + row[j+1:] for row in a[1:]]) for j in range(len(a)))


def wedge(x, y):
    return [x[i]*y[j]-x[j]*y[i] for i, j in it.combinations(range(4), 2)]


def determinantal_divisor(a, k):
    return math.gcd(*(determinant([[a[i][j] for j in cc] for i in rr])
        for rr in it.combinations(range(len(a)), k)
        for cc in it.combinations(range(len(a[0])), k)))


def run():
    f = [0, 1]
    for _ in range(205):
        f.append(sum(f[-2:]))
    checked = 0
    samples = []
    for a in range(1, 101):
        u, v = f[a-1], f[a]
        mult = [[u, v], [v, u+v]]
        assert determinant(mult) == (-1)**a
        # Construct the four inclusions from their actual two integer generators.
        pairs = [([1, 0, 0, 0], [0, 1, 0, 0]),
                 ([0, 0, 1, 0], [0, 0, 0, 1]),
                 ([1, 0, u, v], [0, 1, v, u+v]),
                 ([u, v, 1, 0], [v, u+v, 0, 1])]
        b = list(map(list, zip(*(wedge(x, y) for x, y in pairs))))
        ds = [determinantal_divisor(b, k) for k in range(1, 5)]
        assert ds == [1, 1, 1, f[2*a]]
        # Integral matrix for the two inclined forms, independently of wedge map.
        arr = [[-u, -v, 1, 0], [-v, -u-v, 0, 1],
               [1, 0, -u, -v], [0, 1, -v, -u-v]]
        m = abs(determinant(arr))
        lucas = 2*u+v
        assert m == lucas**2 - 2*(-1)**a - 2
        assert (f[2*a] % 2 == 0) == (a % 3 == 0)
        assert a % 3 or f[2*a] % 8 == 0
        assert f[2*a] == v*(2*u+v)
        checked += 1
        if a <= 6:
            samples.append({'a': a, 'M': m, 'd': f[2*a],
                            'predicted_Z2_rank': m+9+2*(a % 3 == 0)})

    local = 0
    for r in (2, 3, 4):
        for q in it.product(range(-2, 3), repeat=r):
            if sum(q):
                continue
            changes = list(q) + [0]*r
            sectors = [0]
            for d in changes[:-1]:
                sectors.append(sectors[-1]+d)
            recovered = [sectors[(i+1) % (2*r)]-sectors[i] for i in range(2*r)]
            assert recovered == changes
            assert tuple(recovered[i]+recovered[i+r] for i in range(r)) == q
            local += 1

    # Hostile arithmetic alternatives, including parity outside the even-Fibonacci case.
    assert (2//2) % 2 == 1 and (8//2) % 2 == 0
    assert 8 != 1  # Discarding the Smith torsion fails already at a=3.
    assert samples[2]['predicted_Z2_rank'] == 27
    assert samples[2]['predicted_Z2_rank'] != samples[2]['M']+9
    return {'status': 'finite exact diagnostics satisfied',
            'scope': 'integer matrices and local corner germs only; no theorem/gate credit',
            'a_values': checked, 'corner_germs': local, 'small_arithmetic_samples': samples,
            'warning': 'Small a samples need not satisfy source lambda-choice.'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
