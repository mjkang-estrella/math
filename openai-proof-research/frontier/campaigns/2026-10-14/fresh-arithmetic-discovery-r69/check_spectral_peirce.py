#!/usr/bin/env python3
"""Exact integer leading-density and limiting-projection diagnostics."""
import itertools,json
from fractions import Fraction as F

def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def add(a,b):return [[x+y for x,y in zip(row,col)] for row,col in zip(a,b)]
def sub(a,b):return [[x-y for x,y in zip(row,col)] for row,col in zip(a,b)]
def comm(a,b):return sub(mul(a,b),mul(b,a))
def dot(a,b):return sum(x*y for row,col in zip(a,b) for x,y in zip(row,col))
def require(a,b,label):
    if a!=b:raise RuntimeError(label)
n=5
w=[[[0]*n for _ in range(n)] for _ in range(n)]
for k in (2,3,4):
    for p in itertools.permutations((0,1,k)):w[p[0]][p[1]][p[2]]=1
e=[[[int(i==j==r) for j in range(n)] for i in range(n)] for r in range(n)]
c=[[add(comm(e[r],w[i]),comm(w[r],e[i])) for i in range(n)] for r in range(n)]
d=[[sum(F(dot(row[i],row[j]),2) for row in c) for j in range(n)] for i in range(n)]
expected=[[12,-3,-1,-1,-1],[-3,12,-1,-1,-1],[-1,-1,4,2,2],[-1,-1,2,4,2],[-1,-1,2,2,4]]
require(d,expected,'leading density')
p=[[F(int(i==j))-F(1,3) if i>=2 and j>=2 else F(0) for j in range(n)] for i in range(n)]
require(mul(p,p),p,'P projection')
require(mul(d,p),[[2*x for x in row] for row in p],'low eigenspace')
h=[[F(1 if i<2 else 1,1 if i<2 else 3) if i==j else F(0) for j in range(n)] for i in range(n)]
left=mul(mul(p,sub(h,[[2*x for x in row] for row in mul(h,h)])),p)
require(left,[[x/9 for x in row] for row in p],'positive Peirce-gap limit')
for v,lam in [([1,-1,0,0,0],15),([1,1,1,1,1],6),([3,3,-2,-2,-2],11)]:
    require([sum(d[i][j]*v[j] for j in range(n)) for i in range(n)],[lam*x for x in v],'remaining eigenvalue')
print(json.dumps({'status':'PASS_EXACT_LEADING_DENSITY_AND_LIMIT_DIAGNOSTICS_ONLY','dimension':5,'spectrum':[2,2,6,11,15],'threshold_coefficient':3,'limiting_positive_eigenvalue':'1/9','identities_checked':7},indent=2))
