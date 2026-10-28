#!/usr/bin/env python3
"""Exact failed-route and public-prior checks; no discovery is claimed."""
from fractions import Fraction as F
from pathlib import Path
import json
import sympy as sp

def mat(rows):
    return tuple(tuple(F(x) for x in row) for row in rows)

def mul(a,b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))

def sub(a,b,q=1):
    return tuple(tuple(x-q*y for x,y in zip(r,s)) for r,s in zip(a,b))

def inner(a,b):
    return sum(x*y for r,s in zip(a,b) for x,y in zip(r,s))

def mass(a):
    return inner(a,a)

def diagonal(xs):
    return mat([[x if i==j else 0 for j in range(len(xs))]
                for i,x in enumerate(xs)])

def trace(a):
    return sum(a[i][i] for i in range(len(a)))

def c(a,w,b):
    return sub(mul(mul(a,w),b),mul(mul(b,w),a))

x=diagonal([2,-1]); y=mat([[0,1],[0,0]])
I=diagonal([1,1]); P=diagonal([1,0]); W=diagonal([2,1])
cross=inner(c(x,I,y),c(x,P,y)); scale=mass(x)*mass(y)
assert cross==6 and scale==5 and cross>scale
assert mass(c(x,W,y))==(F(2)**2+F(1)**2)*scale==25
a,b=sp.symbols('a b',real=True)
assert sp.expand(5*(a*a+b*b)-(2*a+b)**2-(a-2*b)**2)==0

# Public negative-q counterexample: recompute the literal source coefficient.
A=diagonal([2,-1,-1]); B=diagonal([1,0,0]); q=F(-1); n=F(3)
g=(n*n-3*n+3)/(n*(n-1))
lhs=mass(sub(mul(A,B),mul(B,A),q))
rhs=max(g*(1-q)**2,1+q*q)*mass(A)*mass(B)
assert trace(A)==0 and lhs==16 and rhs==12

# Public positive-q example: both traces vanish (not a trace-condition loophole).
A=mat([[6,42,0,0,0],[0,-3,0,0,0],[0,0,-1,0,0],
       [0,0,0,-1,0],[0,0,0,0,-1]])
B=mat([[6,0,0,0,0],[-42,-3,0,0,0],[0,0,-1,0,0],
       [0,0,0,-1,0],[0,0,0,0,-1]])
q=F(2)
lhs2=mass(sub(mul(A,B),mul(B,A),q)); rhs2=(1+q*q)*mass(A)*mass(B)
assert trace(A)==trace(B)==0
assert mass(A)==mass(B)==1812
assert lhs2==16417164 and rhs2==16416720 and lhs2-rhs2==444

# Algebraic decomposition for a future mixed-BW route. This is an identity,
# not the unproved circular joint-range bound discussed in FINDINGS.md.
u,v,z,q=sp.symbols('u v z q',real=True)
s=u+v-2*z; d=u-v
assert sp.expand(u+q*v-(1+q)*z-((1+q)*s+(1-q)*d)/2)==0

result={
 'status':'PASS exact computations; no eligible discovery',
 'failed_mixed_estimate':{'cross':str(cross),'proposed_rhs':str(scale),
                           'ratio':str(cross/scale)},
 'weighted_target_not_refuted':{'lhs':25,'rhs':25},
 'public_negative_q':{'lhs':str(lhs),'rhs':str(rhs)},
 'public_positive_q':{'lhs':str(lhs2),'rhs':str(rhs2),'gap':444},
 'symbolic_identities':2,'new_theorem_claimed':False,'credit':0}
Path(__file__).with_name('exact-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
