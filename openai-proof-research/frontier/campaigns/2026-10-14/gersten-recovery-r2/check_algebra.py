#!/usr/bin/env python3
"""Exact finite-field diagnostic; not a K-theory or G4 proof. MIT."""
import json
from math import comb

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def rem(a,b):
    a=trim([x%5 for x in a]);b=trim(b[:])
    while len(a)>=len(b) and any(a):
        k=len(a)-len(b);c=a[-1]*pow(b[-1],-1,5)%5
        for j in range(len(b)):a[j+k]=(a[j+k]-c*b[j])%5
        trim(a)
    return a

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return rem(c,[1,4,0,0,0,1])

def power(a,n):
    b=[1]
    while n:
        if n&1:b=mul(a,b)
        a=mul(a,a);n//=2
    return b

# In F5[s]/(s^5-s+1), Frobenius sends s to s-1.
orbit=[power([0,1],5**r) for r in range(1,6)]
assert orbit==[[4,1],[3,1],[2,1],[1,1],[0,1]]
# Polynomial degree five, every root's orbit five: irreducible.
# Intermediate coefficients of (x-1)^5 vanish modulo 5.
coeff=[comb(5,k)*(-1)**(5-k) for k in range(6)]
assert [v%5 for v in coeff]==[4,0,0,0,0,1]
# Constant term zeta-1=-pi and degree five yield norm +pi.
assert coeff[0]==-1 and (-1)**5*(-1)==1
print(json.dumps({'result':'EXACT_POLYNOMIAL_CHECKS_PASS','frobenius_orbit':orbit,'residue_degree':5,'constant_field_cardinality':5**5,'limits':'No K-theory class nonvanishing established.'},sort_keys=True))
