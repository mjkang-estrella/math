#!/usr/bin/env python3
"""Finite bookkeeping only; no flow/holonomy/uniformization certification."""
from fractions import Fraction as Q
from itertools import product
import json

def run():
    checks=[]
    # Unnormalized rotation, avoiding irrational sqrt(2): normalized result /4.
    v=(Q(1),Q(1));w=(Q(1),Q(-1))
    for h1,h2 in [(Q(1),Q(1)),(Q(2),Q(3)),(Q(1,7),Q(13,11))]:
        R={(0,0,0,0):h1,(1,1,1,1):h2}
        B=sum(R.get((i,j,k,l),0)*v[i]*v[j]*w[k]*w[l] for i,j,k,l in product(range(2),repeat=4))
        assert B/4==(h1+h2)/4>0
        checks.append('zero-mixed rotation '+str((h1,h2)))
    for n in range(1,6):
        eigen=[Q(1,i+1) for i in range(n)]
        det=Q(1)
        for x in eigen:det*=x
        assert all(0<det/x<=1 for x in eigen)
        checks.append('cofactor dimension '+str(n))
    # Scalar mass tail exponent used by the source comparison.
    for n in range(1,6):
        k=2*n+4
        assert 2*n-1-k==-5
        checks.append('comparison shell dimension '+str(n))
    # A positive Hessian addition need not preserve curvature at a flat point.
    for eps,A in [(Q(1,10),Q(1)),(Q(1,1000),Q(99))]:
        assert 1+eps>0 and -4*eps*A<0
        checks.append('fourth-jet obstruction '+str((eps,A)))
    return {'status':'PASS_FINITE_BOOKKEEPING_ONLY','checks':checks,'count':len(checks),'full_theorem_verified':False}
if __name__=='__main__':print(json.dumps(run(),indent=2))
