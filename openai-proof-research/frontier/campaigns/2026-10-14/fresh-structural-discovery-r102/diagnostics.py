#!/usr/bin/env python3
"""Bounded author diagnostics. Not proof, source replay, or review."""
from fractions import Fraction as F
from math import sqrt,lgamma,log,exp
import json
checks=0
for d in range(1,33):
    # S=sqrt(2)T. Multiply integer slices exactly, then divide by2.
    slices=[]
    for r in range(d+1):
        a={}
        if r==0:
            a={(i,i):1 for i in range(1,d+1)}
        else:a={(0,r):1,(r,0):1}
        slices.append(a)
    B={}
    for a in slices:
        for (i,j),v in a.items():
            for (k,l),w in a.items():
                if j==k:B[i,l]=B.get((i,l),F(0))+F(v*w,2)
    assert B=={(i,i):F(d,2) if i==0 else F(1) for i in range(d+1)}
    mixed=sum(F(v*v,2) for a in slices for (i,j),v in a.items() if i>0 and j==0)
    assert mixed==F(d,2)
    checks+=2
rows=[]
for n in [2,3,4,10,100,1000]:
    c=sqrt(n*(n+1));a=((c-n)**2+n)*(n-1)/(n*(n+1))
    cost=(sqrt(a)+sqrt(2*(1-1/sqrt(n))))**2
    deficit=.5*log(n)+.5*(n-1)*log(n*(n+1))-lgamma(n)-(n-1)
    assert 0<a<1 and cost<6 and deficit>0
    rows.append({'n':n,'simplex_deficit_float':deficit,'coupling_bound_float':cost})
    checks+=3
    for p in [1,1.5,2,4,10,100]:
        # E R^k=Gamma((n+k)/p)/Gamma(n/p) for density r^(n-1)e^(-r^p).
        ratio=exp(lgamma((n+2)/p)+lgamma(n/p)-2*lgamma((n+1)/p))
        assert ratio<=1+1/n+1e-10
        tangent=2*(n-1)*(1-sqrt(n/(n+1))/sqrt(ratio))
        assert -1e-8<=tangent<=2+1e-7
        checks+=2
print(json.dumps({'status':'PASS','scalar_assertions':checks,'scope':'32 exact star identities and mixed energies; six simplex diagnostics; 36 radial gamma cases. No numerical curl integration or general theorem verification.','simplex':rows},indent=2))
