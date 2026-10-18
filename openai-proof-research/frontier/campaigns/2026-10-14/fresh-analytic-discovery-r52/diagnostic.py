#!/usr/bin/env python3
# MIT. Finite rational checks only; not proof of any analytic assertion.
from fractions import Fraction as F
from itertools import product

def exponent(a,b,z):
    m=(a+b)/2;e=(a-b)/2
    return 2*((z-m)**2-e**2),z*z+(z-a-b)**2-a*a-b*b
for a,b,z in product(map(F,range(-3,4)),repeat=3):
    x,y=exponent(a,b,z);assert x==y
# The sign of both input energy squares matters.
assert any(exponent(a,b,z)[0] != z*z+(z-a-b)**2+a*a+b*b
           for a,b,z in product(map(F,range(-2,3)),repeat=3))
a,b,eps=F(1,4),F(1,8),F(1,32)
assert 0<b<a<F(1,3) and 3*eps<a
assert 1-3*a>0
mix=(1+eps)/(1+b-a+eps)
assert mix>1
# Deliberate invalid L2 and stripe regimes are rejected.
assert not (1-3*F(1,2)>0)
assert not (0<F(1,3)<a)
# The spatial barrier sum does not gain positive powers of s.
assert -2*eps<0
# Axial-potential contraction, including the sharp parameter boundary.
for e in [F(1,64),F(1,32),F(1,8)]:
    beta=1/(4*e*(1+e));delta=1/(4*beta*e*(1+e))
    assert delta==1
    assert 1/(4*(beta/2)*e*(1+e))>1
print('PASS_FINITE_DIAGNOSTIC_ONLY: exponent identity, valid parameters, and 4 negative controls')
