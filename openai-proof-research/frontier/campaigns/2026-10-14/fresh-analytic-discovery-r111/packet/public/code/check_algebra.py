#!/usr/bin/env python3
"""Finite rational diagnostics only; not mathematical or contribution gates."""
from fractions import Fraction as F
from itertools import permutations, product
import json

def det(rows):
    n=len(rows)
    return sum((-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
               * prod(rows[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def prod(xs):
    out=F(1)
    for x in xs: out*=x
    return out
def cross(x,y): return x[0]*y[1]-x[1]*y[0]
def contact(z): return [z[0]**2,2*z[0]*z[1],z[1]**2]
def four(a,b,u,v):
    return det([contact((x-u,y-v))+[F(1)] for x,y in [(0,0),(1,0),(0,1),(a,b)]])
def poly(a,b,u,v):
    return (2*u-1)*(2*u*b*(b-1)-2*a*b*(2*v-1))+2*v*(2*v-1)*a*(a-1)

def main():
    vals=list(map(F,[-1,0,1])); vectors=list(product(vals,repeat=2)); n3=0
    for z in product(vectors,repeat=3):
        assert det([contact(t) for t in z])==2*cross(z[0],z[1])*cross(z[0],z[2])*cross(z[1],z[2]); n3+=1
    vals=list(map(F,[-2,-1,0,1,2])); n4=0
    for a,b,u,v in product(vals,repeat=4):
        assert four(a,b,u,v)==-poly(a,b,u,v); n4+=1
    witnesses=[((F(1),F(0)),(F(0),F(1)),(F(1),F(1))),
               ((F(2),F(1)),(F(-1),F(2)),(F(3),F(-2)))]
    assert all(det([contact(t) for t in z])!=cross(z[0],z[1])*cross(z[0],z[2])*cross(z[1],z[2]) for z in witnesses)
    assert four(F(2),F(3),F(0),F(0))!=poly(F(2),F(3),F(0),F(0))
    assert det([contact(t) for t in [(1,0),(-1,0),(0,1)]])==0
    print(json.dumps({'kind':'finite rational diagnostics; not a mathematical gate',
      'three_contact_cases':n3,'four_contact_cases':n4,
      'controls':{'missing_factor_two_rejected':True,'wrong_four_contact_sign_rejected':True,
                  'antipodal_degeneracy_retained':True},'all_checks_passed':True},sort_keys=True,indent=2))
if __name__=='__main__': main()
