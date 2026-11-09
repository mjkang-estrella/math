#!/usr/bin/env python3
"""Exact finite checks only; the all-order deduction is in PROOF.md."""
from fractions import Fraction as F
from math import factorial
import json
from pathlib import Path

p = Path(__file__).resolve().parent
u = [F(1), F(0)]
for n in range(2, 101):
    u.append(sum(u[n-j] / (j*(j-1)) for j in range(2, n+1)))
b = [u[0]] + [u[n]-u[n-1] for n in range(1, len(u))]
assert b[3] == -F(1, 3)
assert b[12] == -F(10819, 9979200) < -F(1, 2000)
assert b[14] == -F(3676549, 1816214400) < b[12]
assert (-1)**11*b[11]*factorial(11) == 319296
assert b[12]*factorial(12) == -519312
assert all(x < 0 for x in b[11:])

J = sum(((1+F(1, 2**k))**(-12) -
         (1+F(1, 2**(k-1)))**(-12)) /
        (12*((1+F(7*k, 10))**2+10)) for k in range(2, 7))
pole_upper = F(2719, 1000)/(F(2718, 1000)-1)**13
assert J > F(1, 400) > pole_upper

rows = []
for N in [2, 4, 8, 16, 32, 64, 128, 256, 512]:
    moments = [F(sum(i**k for i in range(N)), N**(k+1)) for k in range(14)]
    probs = {j: moments[j-2]-moments[j-1] for j in range(2, 15)}
    a = [F(1), F(0)]
    for n in range(2, 15):
        a.append(sum(probs[j]*a[n-j] for j in range(2, n+1)))
    d = [a[0]] + [a[i]-a[i-1] for i in range(1, 15)]
    rows.append({'N': N, 'b3': str(d[3]), 'b12': str(d[12]),
                 'b14': str(d[14]), 'second_moment': str(1-moments[1]),
                 'criterion_holds': d[12] < -F(1, 2000) and d[14] < d[12]
                                    and d[3] < -F(1, 4)})
assert all(row['criterion_holds'] for row in rows if row['N'] >= 128)
result = {'status': 'PASS: finite rational checks only', 'credit': 0,
          'b3': str(b[3]), 'b12': str(b[12]), 'b14': str(b[14]),
          'analytic_cutoff_J': str(J), 'pole_upper': str(pole_upper),
          'finite_matrices': rows}
(p/'exact-check-replay.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: result[key] for key in ['status', 'credit', 'b3', 'b12', 'b14']},
                 indent=2))
