#!/usr/bin/env python3
"""Finite diagnostics for the exact Gram-completion construction."""
import itertools
import json
import math

def dot(a,b):
    return sum(x*y for row,col in zip(a,b) for x,y in zip(row,col))
def case(a,c,d):
    m=3
    s=[[[0.]*m for _ in range(m)] for _ in range(m)]
    s[0][0][0]=a
    for p in set(itertools.permutations((0,1,1))):
        s[p[0]][p[1]][p[2]]=c
    s[2][2][2]=d
    gram=[[dot(x,y) for y in s] for x in s]
    deficit=[1-gram[i][i] for i in range(m)]
    if min(deficit)<0 or any(abs(gram[i][j])>1e-12 for i in range(m) for j in range(m) if i!=j):
        raise RuntimeError('test input contract')
    n=m+2*m
    t=[[[0.]*n for _ in range(n)] for _ in range(n)]
    for i,j,k in itertools.product(range(m),repeat=3):
        t[i][j][k]=s[i][j][k]
    cost=0.
    for i,e in enumerate(deficit):
        u=m+2*i;w=u+1;l=math.sqrt(e/2);z=math.sqrt(1-e)
        for p in itertools.permutations((i,u,w)):
            t[p[0]][p[1]][p[2]]=l
        t[u][u][u]=t[w][w][w]=z
        cost+=6*l*l+2*(1-z)**2
    error=max(abs(dot(t[i],t[j])-float(i==j)) for i in range(n) for j in range(n))
    if error>1e-12 or cost>5*sum(deficit)+1e-12:
        raise RuntimeError('Gram extension identity')
    return {'input': [a,c,d], 'extended_dimension':n,'Gram_error':error,'cost':cost,'trace_deficit':sum(deficit)}
if __name__=='__main__':
    print(json.dumps({'status':'PASS_FINITE_EXTENSION_DIAGNOSTICS_ONLY','cases':[case(.5,.2,.8),case(.8,.3,1.),case(0.,.5,.2)]},indent=2))
