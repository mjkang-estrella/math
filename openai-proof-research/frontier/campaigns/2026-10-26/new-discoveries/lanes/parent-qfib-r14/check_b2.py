#!/usr/bin/env python3
"""Exact finite checks of the classical B2 specialization (not a new theorem)."""
import json
from pathlib import Path


def coefficients(a, b):
    lengths = [a, b, a+b, a+2*b]
    degree = sum(lengths)-7
    # Denominator of the (1-q^length) product is (1-q)^2(1-q^2)(1-q^3).
    result = [1]+[0]*degree
    for weight in [1, 1, 2, 3]:
        for k in range(weight, degree+1):
            result[k] += result[k-weight]
    for length in lengths:
        for k in range(degree, length-1, -1):
            result[k] -= result[k-length]
    return result


checks = 0
for a in range(1, 51):
    for b in range(1, 51):
        c = coefficients(a, b)
        assert min(c) >= 0 and c == c[::-1]
        assert all(c[k] <= c[k+1] for k in range((len(c)-1)//2))
        # Weyl dimension limit for the four coroot pairings.
        assert 6*sum(c) == a*b*(a+b)*(a+2*b)
        checks += 1

f = [0, 1]
for _ in range(15):
    f.append(sum(f[-2:]))
for m in range(11):
    a, b = f[m+1:m+3]
    assert [a,b,a+b,a+2*b] == f[m+1:m+5]

result = {'status': 'PASS finite exact evidence only; general proof is classical',
          'parameter_pairs_checked': checks, 'fibonacci_specializations_checked': 11,
          'coroot_coordinates': [[1,0],[0,1],[1,1],[1,2]],
          'denominator_heights': [1,1,2,3],
          'degree': '3*a+4*b-7', 'discovery_credit': 0}
out = json.dumps(result, indent=2)+'\n'
Path(__file__).with_name('b2-check.json').write_text(out)
print(out, end='')
