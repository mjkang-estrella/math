#!/usr/bin/env python3
# MIT. Exact finite algebra/negative controls only; not a proof of T337E.
from fractions import Fraction as Q
import json
for j in range(1,201):
    r=Q(j,100);w2=r*r-r**4/4;h=r*r/2
    assert w2>=0
    assert w2+(h-1)**2==1
    assert w2+h*h==r*r
# Wrong height normalization breaks the offset-sphere identity.
r=Q(1);w2=Q(3,4)
assert w2+(r*r/3-1)**2!=1
# Two derivative inequalities and opposite Busemann bound: signs matter.
# a+=a-=−1 is the tripod's third branch. No linear ell can satisfy both
# ell>=1 and -ell>=1. Merely |ell|<=1 would miss this obstruction.
assert -Q(-1)-Q(-1)>0
# Diameter 2 does not force circumradius<=1: regular tetrahedron has R²=3/2.
assert Q(3,2)>1
# Multiplicity k ball: mass-volume equality requires k=k^((n+1)/n).
# Taking n-th powers avoids irrational arithmetic.
for n in range(2,16):
    for k in range(1,9):
        assert (k**n==k**(n+1))==(k==1)
# Remote sheets can cancel despite a nonzero differential on each sheet.
assert sum([1,-1])==0
# The actual proof excludes remote sheets by exact radial preservation.
assert Q(2)>0  # remote copy distance, while its projected distance is zero
print(json.dumps({'diagnostic_only':True,'rational_sphere_samples':200,
 'negative_controls':['wrong height rejected','tripod opposite-direction incompatibility',
 'diameter-to-radius shortcut rejected','multiplicity>1 equality rejected',
 'nonzero local Jacobian alone permits remote cancellation']},indent=2))
