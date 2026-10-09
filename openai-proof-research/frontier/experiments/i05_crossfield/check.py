"""Finite falsification checks, NOT a proof of the analytic theorem."""
import json, math, random
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
random.seed(51008)

# Squarefree polynomial ring in t variables modulo t_i^2=0, exact rationals.
# This truncation preserves the coefficient of t_1...t_D in a full MGF.
def add(A,B):
    C=A.copy()
    for m,c in B.items():C[m]=C.get(m,F(0))+c
    return {m:c for m,c in C.items() if c}
def scale(A,c):return {m:a*c for m,a in A.items() if a*c}
def mul(A,B):
    C={}
    for m,a in A.items():
        for n,b in B.items():
            if not m&n:C[m|n]=C.get(m|n,F(0))+a*b
    return {m:c for m,c in C.items() if c}
rows=[]
for D in range(1,9):
    h=[[F(random.randrange(-3,4),random.randrange(1,4)) for _ in range(3)] for _ in range(D)]
    G=[[sum(a*b for a,b in zip(u,v)) for v in h] for u in h]
    x=[F(random.randrange(-4,5),3) for _ in range(D)]
    @lru_cache(None)
    def wick(I):
        if not I:return F(1)
        a,*rest=I
        return x[a]*wick(tuple(rest))-sum(G[a][b]*wick(tuple(c for c in rest if c!=b)) for b in rest)
    # Y_i=sqrt(D) W_i(h_i), conditioned on W0:
    # mean x_i, covariance D*delta_ij*G_ii-G_ij.
    # Diagonal quadratic MGF terms disappear in the squarefree quotient.
    Q={1<<i:x[i] for i in range(D)}
    Q.update({(1<<i)|(1<<j):-G[i][j] for i in range(D) for j in range(i+1,D)})
    expQ={0:F(1)}; power={0:F(1)}
    for k in range(1,D+1):
        power=mul(power,Q);expQ=add(expQ,scale(power,F(1,math.factorial(k))))
    value=expQ.get((1<<D)-1,F(0))
    assert value==wick(tuple(range(D)))
    rows.append({'degree':D,'conditional_scaled_moment':str(value),'pass':True})

# Full ordinary-product/Wick-contraction expansion, symbolic squarefree x.
counts=[]
def partial_pairings(I):
    if not I:
        yield (),();return
    a,*rest=I
    for pairs,unpaired in partial_pairings(tuple(rest)):
        yield pairs,(a,)+unpaired
    for b in rest:
        for pairs,unpaired in partial_pairings(tuple(c for c in rest if c!=b)):
            yield ((a,b),)+pairs,unpaired
for D in range(1,9):
    G=[[F((i+1)*(j+1)+1,7) for j in range(D)] for i in range(D)]
    @lru_cache(None)
    def W(I):
        if not I:return {0:F(1)}
        a,*rest=I
        result=mul({1<<a:F(1)},W(tuple(rest)))
        for b in rest:result=add(result,scale(W(tuple(c for c in rest if c!=b)),-G[a][b]))
        return result
    terms=list(partial_pairings(tuple(range(D))))
    expansion={}
    for pairs,unpaired in terms:
        expansion=add(expansion,scale(W(unpaired),math.prod(G[a][b] for a,b in pairs)))
    assert expansion=={(1<<D)-1:F(1)}
    counts.append({'degree':D,'pairing_terms':len(terms),'pass':True})

# Finite Gaussian action: U is the cyclic coordinate permutation on R^5.
# Coordinate evaluation is rational; no random convergence claim is made.
v=[F(-2),F(1,2),F(3),F(4,3),F(-1)]
def z(n):
    return (v[(n*n)%5]**2-1)*v[(2*n*n+1)%5]*v[(3*n*n+2)%5]
period=sum(z(n) for n in range(1,6))/5
for N in [5,10,25,50,100]:assert sum(z(n) for n in range(1,N+1))/N==period

# Conditional Minkowski variation check on finite probability partitions.
# Dynamic programming maximizes sum |a[j]-a[i]|^4 over every subsequence.
def V(a):
    dp=[0.]*len(a)
    for j in range(1,len(a)):dp[j]=max([0.]+[dp[i]+abs(a[j]-a[i])**4 for i in range(j)])
    return max(dp)**.25
max_ratio=0.
for _ in range(300):
    arr=[[random.uniform(-3,3) for _ in range(15)] for _ in range(5)]
    lhs=V([sum(a[j] for a in arr)/5 for j in range(15)])
    rhs=sum(V(a) for a in arr)/5
    assert lhs<=rhs+1e-12
    max_ratio=max(max_ratio,lhs/rhs)

out={'conditional_MGF_checks':rows,'symbolic_Wick_expansions':counts,'cyclic_action':{'period':5,'exact_limit':str(period),'lengths':[5,10,25,50,100]},'conditional_variation':{'trials':300,'length':15,'largest_ratio':round(max_ratio,10)},'scope':'Finite normalization, contraction-sign, and averaging checks only. No universal convergence or novelty certification.'}
print(json.dumps(out,indent=2))
