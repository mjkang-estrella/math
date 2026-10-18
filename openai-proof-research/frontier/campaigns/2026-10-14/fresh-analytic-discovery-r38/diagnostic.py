#!/usr/bin/env python3
"""MIT. Finite exact route checks, not a proof of the frozen field target."""
from fractions import Fraction as F
from collections import Counter
import json
V=list(range(6))
# (0,1,2) bottom; (3,4,5) top. Outer verticals last.
E=[(0,1),(1,2),(3,4),(4,5),(1,4),(0,3),(2,5)]
def weight(mask):
    parent=list(V)
    def root(v):
        while parent[v]!=v:v=parent[v]
        return v
    for i,(a,b) in enumerate(E):
        if mask>>i&1:parent[root(a)]=root(b)
    components=len({root(v) for v in V}); out=Counter();sub=mask
    while True:
        parity=[0]*6
        for i,(a,b) in enumerate(E):
            if sub>>i&1:parity[a]^=1;parity[b]^=1
        if not any(parity):out[mask.bit_count()-sub.bit_count()]+=2**components
        if not sub:break
        sub=(sub-1)&mask
    return dict(out)
def mul(a,b):
    out=Counter()
    for i,x in a.items():
        for j,y in b.items():out[i+j]+=x*y
    return dict(out)
def subtract(a,b):
    return {i:a.get(i,0)-b.get(i,0) for i in a.keys()|b.keys() if a.get(i,0)!=b.get(i,0)}
def ev(poly,y):return sum(c*y**d for d,c in poly.items())
W=[weight(31 | (l<<5) | (r<<6)) for l,r in [(0,0),(1,0),(0,1),(1,1)]]
assert W==[{5:2},{6:2,2:2},{6:2,2:2},{7:2,3:4,1:2}]
det=subtract(mul(W[0],W[3]),mul(W[1],W[2]));assert det=={6:4,4:-4}
interior=[]
for d in range(2,21):
    for n in range(1,d):
        y=F(n,d);value=ev(det,y);assert value<0;interior.append(value)
assert ev(det,F(1))==0
# Incorrect unconditional FKG transfer must fail, as a strict determinant test.
assert not (ev(det,F(1,2))>=0)
# Incorrect endpoint strict negativity must fail.
assert not (ev(det,F(1))<0)
# Independent bounded lattice noise: E epsilon=0, E(-1)^epsilon=0, Var=1/2.
law={-1:F(1,4),0:F(1,2),1:F(1,4)}
assert sum(F(k)*p for k,p in law.items())==0
assert sum(F((-1)**k)*p for k,p in law.items())==0
assert sum(F(k*k)*p for k,p in law.items())==F(1,2)
# At mesh1/n on a unit-square n² lattice, unit-test perturbation variance1/(2n²).
for n in range(2,41):
    assert F(1,n)**4*n*n*F(1,2)==F(1,2*n*n)
print(json.dumps({'status':'PASS_FINITE_ROUTE_DIAGNOSTIC_ONLY','support_weights':W,'determinant_coefficients':det,'rational_interior_checks':len(interior),'negative_controls_rejected':['conditional_current_FKG','strict_endpoint_negativity'],'noise_variance_checks':39},sort_keys=True))
