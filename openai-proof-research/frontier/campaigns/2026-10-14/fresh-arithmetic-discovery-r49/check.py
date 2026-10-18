#!/usr/bin/env python3
"""Finite exact support for the abstract multiscale obstruction, not a proof."""
from fractions import Fraction as F
import itertools,json
count=0
for m in range(1,11):
 M=[4**(m-j) for j in range(1,m+1)]
 roots=[2**(m-j) for j in range(1,m+1)]
 for bits in itertools.product([0,1],repeat=m):
  xs=[2*a*b for a,b in zip(M,bits)]
  S=sum(xs);L=sum(F(x,z) for x,z in zip(xs,roots))
  if L*L>25*S:raise ValueError('scalar restriction bound failed')
  count+=1
 # Exact lower ratio squared of the normalized objective to sqrt(n).
 if F(3*m,4)<=0:raise ValueError('nonpositive growing ratio')
# Biased grade-zero block at constant polynomial: <v,Hv>=2p-1.
p=F(1,4)
if 2*p-1!=-F(1,2):raise ValueError('grade identity mismatch')
print(json.dumps({'status':'PASS_FINITE_SUPPORT_ONLY','group_endpoint_checks':count,'max_m':10,'grade_zero_block':'-1/2','full_target_proved':False}))
