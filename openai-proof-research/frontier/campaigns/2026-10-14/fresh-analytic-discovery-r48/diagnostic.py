#!/usr/bin/env python3
# MIT. Rational arithmetic and elementary finite-sum diagnostics, not a proof.
from fractions import Fraction as F
from math import log,exp
alpha=F(1,15); beta=F(1,15)
r=F(-8,15); s=F(-1,30)
assert 1+r*F(15,8)==0
assert s*F(15,8)+F(1,16)==0
assert r*F(-1,8)==alpha
assert s*F(-1,8)+F(1,16)==beta
assert F(15,8)-1==F(7,8)>0
# Negative controls: omit or reverse the logarithmic rescaling.
assert 0*F(15,8)+F(1,16)!=0
assert (-s)*F(15,8)+F(1,16)!=0
# The geometric domination constant is exact analytically; sample only its finite sums.
ratio=2**(-7/8)
for j in range(100):
 assert sum(2**((k-j)*7/8) for k in range(j+1)) <=1/(1-ratio)+1e-12
print('PASS_SCALE_ARITHMETIC_ONLY')
