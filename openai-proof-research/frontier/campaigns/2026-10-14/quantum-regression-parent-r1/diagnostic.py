#!/usr/bin/env python3
"""MIT. Exact rational matrix checks, not proof of the analytic estimate."""
from fractions import Fraction as Q

def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def tr(a): return a[0][0]+a[1][1]
def outer(v):
    n=sum(x*x for x in v)
    return [[Q(x*y,n) for y in v] for x in v]

A,B,C,T=map(outer,[(1,0),(1,1),(1,-2),(2,1)])
for p in [A,B,C,T]:
    assert mul(p,p)==p and tr(p)==1
    assert p[0][1]==p[1][0]
assert tr(mul(mul(A,B),C))==Q(-1,10)
assert tr(mul(mul(A,B),T))==Q(3,5)>tr(mul(A,B))==Q(1,2)
# The two tempting scalar assertions are actually false.
assert not tr(mul(mul(A,B),C))>=0
assert not tr(mul(mul(A,B),T))<=tr(mul(A,B))
for beta,m in [(Q(3,2),1),(Q(7,2),3),(Q(11,2),4)]:
    assert 1+Q(m,1)/(beta-m)==beta/(beta-m)>0
print('PASS_FINITE_DIAGNOSTIC_ONLY: rank-one effects, two failed scalar inferences, layer-cake constant')
