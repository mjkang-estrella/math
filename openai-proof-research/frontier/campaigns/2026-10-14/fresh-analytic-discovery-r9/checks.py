#!/usr/bin/env python3
"""Exact finite support only; does not certify a scaling limit. MIT, Myeongjin Kang."""
from fractions import Fraction as Q
from functools import lru_cache
import json

P={0:Q(9,16),2:Q(3,8),4:Q(1,16)}
assert sum(P.values())==1 and sum(k*p for k,p in P.items())==1

@lru_cache(None)
def trees(n):
    if n==1:return ((),)
    out=[]
    def forests(k,total,prefix=()):
        if k==0:
            if total==0:yield prefix
            return
        for s in range(1,total-k+2,2):
            for t in trees(s):
                yield from forests(k-1,total-s,prefix+(t,))
    for k in (2,4):
        if n>k:out.extend(forests(k,n-1))
    return tuple(out)

@lru_cache(None)
def size(t):return 1+sum(size(c) for c in t)
@lru_cache(None)
def weight(t):
    w=P[len(t)]
    for c in t:w*=weight(c)
    return w

def a(n,z):
    d={0:Q(1)}
    for _ in range(n):
        e={}
        for x,px in d.items():
            for k,pk in P.items():e[x+k-1]=e.get(x+k-1,Q(0))+px*pk
        d=e
    return d.get(z,Q(0))

def additive(t,g,F):
    return g(len(t))*sum((F(size(c)) for c in t),Q(0))+sum((additive(c,g,F) for c in t),Q(0))

cases=0;enumerated=0
for n in range(1,14,2):
    ts=trees(n);enumerated+=len(ts)
    pi=sum((weight(t) for t in ts),Q(0))
    assert pi==a(n,-1)/n
    for g in (lambda k:Q(1),lambda k:Q(k),lambda k:Q(k*(k>2))):
        for F in (lambda s:Q(1),lambda s:Q(s*s),lambda s:Q(s==3),lambda s:Q(s<=5)):
            lhs=sum((weight(t)*additive(t,g,F) for t in ts),Q(0))/pi
            rhs=Q(n)/a(n,-1)*sum((F(s)*a(s,-1)/s*sum((k*p*g(k)*a(n-1-s,1-k) for k,p in P.items()),Q(0)) for s in range(1,n)),Q(0))
            assert lhs==rhs,(n,lhs,rhs)
            cases+=1

# First-passage/zero-remainder convolution underlying selected-child identity.
@lru_cache(None)
def forest_prob(j,n):
    if j==0:return Q(n==0)
    return sum((a(s,-1)/s*forest_prob(j-1,n-s) for s in range(1,n+1,2)),Q(0))
fc=0
for j in range(0,6):
    for m in range(0,18):
        z=sum((forest_prob(j,t)*a(m-t,0) for t in range(m+1)),Q(0))
        assert z==a(m,-j),(j,m,z,a(m,-j));fc+=1

# In-place preorder intervals and indicator integral identity for all small trees.
def intervals(t):
    out=[];index=0
    def rec(x):
        nonlocal index
        left=index;index+=1
        for c in x:rec(c)
        out.append((left,index))
    rec(t);return out
ic=0
for n in range(3,12,2):
    for t in trees(n):
        ints=[(a,b) for a,b in intervals(t) if a>0]
        # Original-degree cells delete the root; length of a child subtree S/(N-1).
        for cut in ints:
            l,r=cut;s=Q(r-l,n-1)
            assert sum((Q(1,n-1)/s for j in range(1,n) if l<=j<r),Q(0))==1
        # A rational Lipschitz interval test, integrated over descendants.
        phi=lambda l,r:Q(l+r,n-1)+Q((r-l)**2,(n-1)**2)
        lhs=sum((phi(l,r) for l,r in ints),Q(0))
        rhs=sum((Q(1,n-1)*sum((phi(l,r)/Q(r-l,n-1) for l,r in ints if l<=j<r),Q(0)) for j in range(1,n)),Q(0))
        assert lhs==rhs;ic+=1

# Nested rank-ones retain genuine interaction: neither norm nor spectrum is maximum weight.
# I=[0,3/4], J=[0,1/2], R_I=16/3, R_J=4, so both individual norms equal one.
sI,sJ=Q(3,4),Q(1,2)
tI,tJ=sI*(1-sI),sJ*(1-sJ)
cov=sJ-sI*sJ
assert cov*cov/(tI*tJ)==Q(1,3)
trace=Q(2);trace_square=Q(2)+2*cov*cov/(tI*tJ)
det=(trace*trace-trace_square)/2
assert det==Q(2,3) and Q(1)-trace+det<0
# The polynomial lambda²-2lambda+2/3 is negative at 1, hence top root >1.

# Exact parent veto: original-degree unit path Rayleigh quotient and cut weight.
path_checks=[]
for n in (2,4,8,16,64):
    m=[1]+[2]*(n-1)+[1]
    M=sum(m);mean=sum(Q(i*w) for i,w in enumerate(m))/M
    var=sum((w*(Q(i)-mean)**2 for i,w in enumerate(m)),Q(0))
    rayleigh=var/n
    assert rayleigh==Q(n*n+2,6)
    cuts=[Q(2*k-1)*(1-Q(2*k-1,M)) for k in range(1,n+1)]
    path_checks.append({'edges':n,'rayleigh':str(rayleigh),'max_cut':str(max(cuts))})

# Exact spine mean for link/opposite-child label: only one of k=2 children, link chance 1/2.
theta=P[2]/2
assert sum((p*sum((Q(1,2) if k==2 and i==2 else Q(0) for i in range(1,k+1)),Q(0)) for k,p in P.items()),Q(0))==theta

print(json.dumps({'status':'PASS_EXACT_FINITE_SUPPORT_ONLY','offspring':{str(k):str(v) for k,v in P.items()},'conditioned_identity_cases':cases,'trees_enumerated':enumerated,'forest_convolution_cases':fc,'interval_integral_trees':ic,'nested_rank_two_characteristic':['1','-2','2/3'],'path_veto':path_checks,'spine_mean':str(theta),'limits_proved_by_computation':False},sort_keys=True,indent=2))
