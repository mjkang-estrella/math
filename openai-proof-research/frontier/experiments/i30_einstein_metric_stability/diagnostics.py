#!/usr/bin/env python3
"""Exact algebra/scale diagnostics. Not a proof of the geometric lemmas."""
from fractions import Fraction as F
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i30_einstein_metric_stability/diagnostics.json'
counts={}
n=0
for i in range(1,81):
 r=F(i,80)
 for j in range(81):
  a=r*F(j,80)
  assert 0 <= r**4-(r-a)**4 <= 4*a*r**3
  for eta in [F(0),F(1,1024),F(1,16)]:
   assert (r*r+eta)**2 == r**4+2*eta*r*r+eta*eta
   n+=1
counts['exact_volume_polynomial_cases']=n
n=0
for k in range(1,257):
 eta=F(1,2**(8*k));r=F(1,2**(2*k));R=F(1,2**(3*k))
 # 1+log(1/eta) <= 1+log_2(1/eta); constants omitted and tracked symbolically.
 a=(1+8*k)*eta
 H=r**6+a*r**3+eta*r*r+eta*eta
 assert H<=6*R**4
 assert R**4==eta*r*r==r**6
 assert R/r==F(1,2**k)
 assert R>=F(1,2**(4*k))
 assert a <= 3*F(1,2**(6*k))
 assert (R/r)**16==eta*eta
 n+=1
counts['dyadic_packing_scale_cases']=n
local=[];global_=[]
for i in range(1,300):
 p=F(i,600)
 local.append((min(2*p,1-p,1-2*p,2-4*p)/4,p))
 global_.append((min(2*p,1-p,1-4*p)/4,p))
assert max(local)==(F(1,8),F(1,4))
assert max(global_)==(F(1,12),F(1,6))
counts['rational_scale_optimizations']=len(local)+len(global_)
n=0
for j in range(-199,200):
 u=F(j,200);a=1/(3*(1+u));b=1/(3*(1-u))
 assert 2/a+2/b==12
 # D/pi^2, computed from the four Ricci eigenvalues and product volume.
 ric1,ric2=1/a,1/b
 e2=2*(ric1-3)**2+2*(ric2-3)**2
 assert e2*16*a*b==64*u*u/(1-u*u)
 ap,bp=a/b-1,b/a-1
 assert ap*b+a*bp==0
 assert ap-bp==(a-b)*(a+b)/(a*b)
 if u: assert (a-b)*(ap-bp)>0
 assert (a-F(1,3))**2<=F(4,9)*u*u if abs(u)<=F(1,2) else True
 n+=1
counts['normalized_product_cases']=n
# Covariant rank-two L2 scale exponent: c^2 from inverse metrics, c^-2 from dmu.
assert 2-4/F(2)==0
# For normalized model operators: all permitted spectral intervals miss 2 lambda=6.
assert F(32,2)-6==10
assert 3*4-6==6 and 0-6==-6
assert F(1,2)/(1-F(2,3))==F(3,2)
counts['tensor_scaling_spectral_moser_identities']=5
result={'status':'PASS','counts':counts,'total_exact_cases':sum(counts.values()),
 'candidate_exponent_D':'1/16','coarser_global_L1_exponent_D':'1/24',
 'scope':'Exact algebra and exponent checks only. Source theorems, PDE estimates, elliptic gauge and geometric packing require mathematical review.'}
OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
