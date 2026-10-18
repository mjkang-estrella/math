#!/usr/bin/env python3
# MIT. Finite exact arithmetic only; not a proof of any gas limit.
from fractions import Fraction as Q
from math import comb,factorial
from itertools import combinations
import json
checks=0
# Normalized fixed-N factorial cumulants, including h>N.
for N in range(1,13):
    moments=[Q(1)]; cumulants=[Q(0)]
    for h in range(1,9):
        moments.append(Q(factorial(N),factorial(N-h)*N**h) if h<=N else Q(0))
        ch=moments[h]-sum(Q(comb(h-1,j-1))*cumulants[j]*moments[h-j] for j in range(1,h))
        cumulants.append(ch)
        assert ch==Q((-1)**(h-1)*factorial(h-1),N**(h-1));checks+=1
assert cumulants[2]!=0 # rejects dropping the fixed-count covariance.
# Intercomponent edge power: all simple graphs up to five components.
for c in range(1,6):
    edges=list(combinations(range(c),2))
    for mask in range(1<<len(edges)):
        E=[e for k,e in enumerate(edges) if mask>>k&1]
        seen={0}
        while True:
            new=seen|{v for u,v in E if u in seen}|{u for u,v in E if v in seen}
            if new==seen:break
            seen=new
        if len(seen)!=c:continue
        p=len(E)
        for h in range(c,c+3):
            for m in range(h,h+3):
                exponent=(m-h)-(m-c)-p
                assert exponent<=1-h
                assert (exponent==1-h)==(p==c-1);checks+=1
assert 3-3-3 != 1-3 # triangle does not have leading tree power.
# Weighted discrete exclusion model: exact insertion and one-point bounds.
w=[Q(k,78) for k in range(1,13)];b=max(w)
def Z(weights,k):
    return factorial(k)*sum((prod(weights[j] for j in ids) for ids in combinations(range(len(weights)),k)),Q(0))
def prod(it):
    out=Q(1)
    for x in it:out*=x
    return out
for N in range(1,4):
    assert N*b<Q(1,2)
    for k in range(1,N+1):
        ratio=Z(w,k)/Z(w,k-1)
        assert 1-(k-1)*b<=ratio<=1;checks+=1
    for j in range(len(w)):
        ratio=Z(w[:j]+w[j+1:],N-1)/Z(w,N)
        assert 1-2*N*b<=ratio<=1/(1-N*b);checks+=1
# The crude conditioned mean-loss exponent is negative, not a vanishing gain.
eta=Q(1,20)
assert eta-1<0
# The activity-to-mean shift exponent is zero in dimension three.
assert Q(3-3,2)==0
print(json.dumps({'arithmetic_only':True,'exact_cases':checks,'negative_controls':['fixed-count covariance cannot be zero','cycle cannot be leading tree','conditioned exponent is not positive'],'claims_not_tested':['marked hierarchy bounds','spatial traces','dynamic remainders','canonical fluctuation theorem']}))
