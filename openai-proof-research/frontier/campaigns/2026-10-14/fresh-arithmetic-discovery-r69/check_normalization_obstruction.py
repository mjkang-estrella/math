#!/usr/bin/env python3
"""Finite diagnostics of explicit Fourier cubic; not a global theorem test."""
import json
import math

def mul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def dot(a,b):
    return sum(x*y for row,col in zip(a,b) for x,y in zip(row,col))
def check(k):
    a=4*k+1;b=2*k;m=a+b
    v=[[math.sqrt(2/a)*f(2*math.pi*l*i/a) for l in range(1,k+1) for f in (math.cos,math.sin)] for i in range(a)]
    t=[[[0.0]*m for _ in range(m)] for _ in range(m)]
    for i in range(a):
        for r in range(b):
            t[i][i][a+r]=t[i][a+r][i]=t[a+r][i][i]=v[i][r]
    gram=[[dot(x,y) for y in t] for x in t]
    error=max(abs(gram[i][j]-(float(i==j)*(2*b/a if i<a else 1))) for i in range(m) for j in range(m))
    c=0.
    for r in range(m):
        for s in range(r+1,m):
            xy=mul(t[r],t[s]);yx=mul(t[s],t[r])
            c+=sum((xy[i][j]-yx[i][j])**2 for i in range(m) for j in range(m))
    predicted=b+b*b/a
    if error>1e-10 or abs(c-predicted)>1e-9:
        raise RuntimeError('Fourier cubic identity failed')
    return {'k':k,'dimension':m,'Gram_max_error':error,'C':c,'C_formula':predicted,'beta_squared':1/a}
if __name__=='__main__':
    print(json.dumps({'status':'PASS_FINITE_FOURIER_IDENTITY_DIAGNOSTICS_ONLY','cases':[check(1),check(2),check(3)]},indent=2))
