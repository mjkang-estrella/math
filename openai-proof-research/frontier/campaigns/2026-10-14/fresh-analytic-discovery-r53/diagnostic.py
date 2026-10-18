#!/usr/bin/env python3
# Myeongjin Kang. MIT. Arithmetic diagnostic only, not a proof.
from fractions import Fraction as Q
# At h1=h2, logsumexp has off-diagonal Hessian -1/4.
# dh1=2du1, dc h2=-du2/2, so coefficient is +1/4.
hessian_cross=-Q(1,4)
coefficient=hessian_cross*2*(-Q(1,2))
assert coefficient==Q(1,4)
# A separable sum has zero mixed Hessian and hence no such obstruction.
assert Q(0)*2*(-Q(1,2))==0
# Weighted lens sequence remains below 3/4 for every k,m tested.
for k in range(1,31):
 for m in range(2,51):
  r=1-Q(1,m)
  assert Q(1,2)*r**(2*k)<Q(3,4)
# Negative controls catch a sign reversal and the false compactness assertion.
for condition in [coefficient==0,coefficient==-Q(1,4),Q(1,2)>=Q(3,4)]:
 assert not condition
print('PASS_NONPROOF_ARITHMETIC; 3 failing assertions rejected')
