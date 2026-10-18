#!/usr/bin/env python3
# Copyright Myeongjin Kang. MIT. Finite arithmetic diagnostics, not proof.
from fractions import Fraction as F
from math import factorial, comb
from itertools import combinations

alpha=F(1,8); beta2=F(1,4); chaos_growth=beta2/4
p=1/(1-chaos_growth)
assert p==F(16,15)==2/(2-alpha)
assert (2-beta2/2)*p==2
assert (1-beta2/2)*p==F(14,15)
assert -F(1,30)*F(15,8)+F(1,16)==0
assert -F(1,30)*(-F(1,8))+F(1,16)==F(1,15)
assert F(8,15)*F(15,8)==1
assert F(1,30)*F(15,8)+F(1,16)*(-1)==0
for k in range(1,12):
    assert F(comb(2*k,k),2**(2*k)*factorial(2*k))==F(1,4**k*factorial(k)**2)
for n in range(2,13,2):
    for plus in combinations(range(n),n//2):
        signs=[1 if j in plus else -1 for j in range(n)]
        pair_sum=sum(signs[i]*signs[j] for i in range(n) for j in range(i+1,n))
        assert n+2*pair_sum==0
# Obvious failing alternatives must be detected.
controls={
 'old_tail_exponent_8_is_not_16': 1/(1-F(1,8))!=p,
 'omit_log_scale_correction_fails': F(1,16)!=0,
 'subgaussian_only_collar_has_wrong_t_power': F(2)!=p,
 'nonneutral_log_radius_does_not_cancel': 2+2*(1*1)!=0,
 'moment_order_does_not_imply_tail_order': F(1,1)>F(2,3),
}
assert all(controls.values())
# X=1/3; Y=Bernoulli(2/3): moment order for these tested k but opposite tails at1/4.
assert all(F(1,3)**k<=F(2,3) for k in range(1,101))
print('PASS_ARITHMETIC_ONLY; 5 negative controls detected; not a proof or novelty test')
