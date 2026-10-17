#!/usr/bin/env python3
"""Exact finite adversarial checks; not a proof of O217. Original code MIT."""
from fractions import Fraction as Q
from itertools import product
from math import comb, factorial
import json

def check():
    gauge_checks=0
    for n in range(2,7):
        edges=[(i,j) for i in range(n) for j in range(i+1,n)]
        for s in product((-1,1),repeat=n):
            for v in range(n):
                t=tuple(-z if i==v else z for i,z in enumerate(s))
                for i,j in edges:
                    gauge_sign=-1 if v in (i,j) else 1
                    assert gauge_sign*t[i]*t[j]==s[i]*s[j]
                    gauge_checks+=1
    # Asymmetric, centered, variance-one rational law.
    law=[(Q(-1,2),Q(4,5)),(Q(2),Q(1,5))]
    moments={k:sum(p*x**k for x,p in law) for k in range(5)}
    assert moments[1]==0 and moments[2]==1 and moments[3]==Q(3,2)
    assert moments[4]==Q(13,4)
    # U=(x12*x13*x23)^3 is gauge-invariant. At x12=0,
    # d12^3 U=6*x13^3*x23^3. It need not have zero expectation.
    odd_mean=sum(px*py*6*x**3*y**3 for x,px in law for y,py in law)
    reflected=sum(px*py*6*(-x)**3*y**3 for x,px in law for y,py in law)
    assert odd_mean==Q(27,2) and reflected==-odd_mean
    assert (odd_mean-reflected)/2==odd_mean
    # Square identity (18), exact for rational jets and arbitrary residual u.
    square_checks=0
    for u,b1,b2,z in product([Q(-3,2),Q(0),Q(2,3)],repeat=4):
        lhs=u*u-b1*b1*z*z-b1*b2*z**3
        rhs=2*b1*z*(u-b1*z-b2*z*z/2)+(u-b1*z)**2
        assert lhs==rhs;square_checks+=1
    # Explicit field breaks the sign gauge. We use exp(h)=2, exp(J)=3.
    def Z(c,field):
        return sum(c**(s*t)*field**(s+t) for s,t in product((-1,1),repeat=2))
    assert Z(Q(3),Q(1))==Z(Q(1,3),Q(1)) # n=2 symmetric-sign deterministic Z
    assert Z(Q(3),Q(2))!=Z(Q(1,3),Q(2)) # no external-field extension
    exponent_checks=0
    for n in range(2,101):
        m=comb(n,2)
        assert Q(m,n*n)<=Q(1,2)
        assert Q(m*n,n**3)<=Q(1,2)
        exponent_checks+=2
    # Bell partition coefficient recurrence for cumulant absolute bound.
    S={(0,0):1}
    for n in range(1,7):
        for k in range(1,n+1):S[n,k]=k*S.get((n-1,k),0)+S.get((n-1,k-1),0)
    B=[sum(S[n,k]*factorial(k-1) for k in range(1,n+1)) for n in range(1,7)]
    assert B==[1,2,6,26,150,1082]
    return {'status':'exact finite checks passed, not universal proof','gauge_edge_checks':gauge_checks,'square_identity_checks':square_checks,'scale_count_checks':exponent_checks,'asymmetric_moments':{str(k):str(v) for k,v in moments.items()},'nonzero_odd_derivative_mean':str(odd_mean),'cumulant_bounds_orders_1_to_6':B,'negative_controls':['asymmetric star law does not annihilate an odd derivative expectation','external field breaks the gauge','n=2 symmetric-sign partition is deterministic']}
if __name__=='__main__':print(json.dumps(check(),indent=2))
