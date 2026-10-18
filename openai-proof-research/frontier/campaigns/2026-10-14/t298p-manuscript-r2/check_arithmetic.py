#!/usr/bin/env python3
"""Exact scalar normalization diagnostics, not an entropy proof. MIT, Myeongjin Kang."""
from fractions import Fraction as Q
import json

rows = []
for k in (2, 3, 4, 2**32):
    n = k*k + 1
    orbit = k*k - 1
    assert n + orbit == 2*k*k
    assert -Q(n, 2) - Q(orbit, 2) + k*k == 0
    assert -Q(n, 2) + Q(n, 2) == 0
    eps = Q(1, 7)
    assert (1/(eps*k*k))**2 == 1/(eps*eps*k**4)
    assert (eps*eps*k*k)/(eps*eps*k**4) == Q(1, k*k)
    assert (1/(eps*k*k))**2 != 1/(eps*eps*k*k)
    rows.append({'k': k, 'n': n, 'orbit': orbit, 'heat_multiplier': str(Q(1, k*k)),
                 'dimension_and_log_cancellation': True, 'wrong_k2_detected': True})
# Finite real scalar example satisfying both increment bounds and endpoint comparison.
c, em, es = Q(1, 4), Q(1, 100), Q(1, 100)
sm0, ss0, sm1, ss1 = Q(0), Q(2), Q(3), Q(7, 2)
m0, m1, st1 = Q(0), Q(3, 4)-em, Q(3, 4)-em
st0 = st1-c*(ss1-ss0)-es
assert m1 <= st1
assert m1-m0 >= c*(sm1-sm0)-em
assert st1-st0 <= c*(ss1-ss0)+es
assert st0-m0 >= c*((ss0-sm0)-(ss1-sm1))-em-es
assert st0 > m0
print(json.dumps({'scope': 'exact finite scalar checks only; analytic hypotheses not established',
                  'normalizations': rows, 'finite_gap_example': True}, indent=2))
