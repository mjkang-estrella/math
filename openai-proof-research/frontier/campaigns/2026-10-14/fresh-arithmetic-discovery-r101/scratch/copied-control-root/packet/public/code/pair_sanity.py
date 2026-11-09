#!/usr/bin/env python3
"""Small exact arithmetic diagnostic; not a proof or mathematical review."""
import json
from math import comb, gcd

def shifted_power(d):
    return [comb(d,j)*(-1)**(d-j) for j in range(d+1)]

def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out

def affine(f,D,b):
    out=[0]*len(f)
    for j,c in enumerate(f):
        for t in range(j+1):out[t]+=c*comb(j,t)*D**t*b**(j-t)
    return out

def family(l):
    return mul(shifted_power(2),mul([1-8*l,8*l],[1-8*l,8*l]))

h=mul(shifted_power(2),[9,6,1])
g=family(1)
assert affine(h,32,-31)==[16384*c for c in g]
n=0
for l in [1,2,3,5,12]:
    f=family(l)
    assert gcd(1-32*l,32*l)==1
    assert affine(g,l,1-l)==[l*l*c for c in f]
    for D in [1,2,3,7]:
        i=D-1
        assert affine(f,D,-i)==[D*D*c for c in family(l*D)]
        assert [1-32*l-32*l*i,32*l*D]==[1-32*l*D,32*l*D]
        n+=1
    for p in [2,3,5,7,11,13]:
        assert any(c%p for c in f[1:])
print(json.dumps({'purpose':'exact example only; no mathematical gate',
 'h_coefficients':h,'D0':32,'r':-31,'M':16384,
 'g_coefficients':g,'coherence_pairs':n,
 'unit_intercepts_and_nonconstant_reductions':'checked on stated finite inputs'},sort_keys=True))
