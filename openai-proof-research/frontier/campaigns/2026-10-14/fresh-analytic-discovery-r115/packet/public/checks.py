#!/usr/bin/env python3
"""Small exact diagnostics only; not proof or contribution gates. No writes."""
from fractions import Fraction as F
import json

# Feynman scalar integral endpoint formula, including the equal endpoint case.
cases = 0
for a in [F(1,3), F(1), F(7,2)]:
    for b in [F(1,3), F(1), F(7,2)]:
        result = 1/(a*a) if a == b else (1/b-1/a)/(a-b)
        assert result == 1/(a*b)
        cases += 1

# Exact negative leading factor H=I, M=diag(1,4).
x, z, mz = (F(1), F(1)), (F(2), F(-1)), (F(2), F(-4))
dot = lambda a,b: sum(v*w for v,w in zip(a,b))
qfactor = dot(x,z)*dot(x,mz)/(dot(x,x)*dot(z,mz))
assert qfactor == F(-1,8)

# A diagonal coordinate projector combination has no mixed coefficient.
x_outer_12 = x[0]*x[1]
assert x_outer_12 == 1

# Lower cutoff and upper energy thresholds are genuinely different for n>4.
for n in range(5,31):
    lo, hi = F(n,n-4), F(n+4,n-4)
    assert lo < hi
    assert n-4*lo/(lo-1) == 0
    assert n-4*(hi+1)/(hi-1) == 0
    mid = (lo+hi)/2
    assert n-4*mid/(mid-1) > 0
    assert n-4*(mid+1)/(mid-1) < 0
    cases += 1

# Torus transition radii and derivative difference, using rational pi factors.
# v1/pi=4/81, R_B^3=3(v1/pi)/4, r_T^2=v1/pi.
assert F(1,3)**3 == F(3,4)*F(4,81)
assert F(2,9)**2 == F(4,81)
assert 2/F(1,3)-1/F(2,9) == F(3,2)
assert 1/F(2,9)**2 == F(81,4)
print(json.dumps(dict(status='finite exact diagnostics completed', scalar_cases=cases,
                      negative_factor=str(qfactor), mathematical_gate=False,
                      contribution_gate=False), sort_keys=True))
