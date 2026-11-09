#!/usr/bin/env python3
"""Finite verification of all blocks in extension-density-blocks.md."""
import itertools,json,math

def mul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def dot(a,b):return sum(x*y for row,col in zip(a,b) for x,y in zip(row,col))
def sub(a,b):return [[x-y for x,y in zip(row,col)] for row,col in zip(a,b)]
def comm(a,b):return sub(mul(a,b),mul(b,a))
def density(x):
    cs=[[comm(r,s) for s in x] for r in x]
    return [[sum(dot(row[i],row[j]) for row in cs)/2 for j in range(len(x))] for i in range(len(x))]
def run(a,c,d):
    m=3;n=9
    s=[[[0.]*m for _ in range(m)] for _ in range(m)]
    s[0][0][0]=a;s[2][2][2]=d
    for p in set(itertools.permutations((0,1,1))):s[p[0]][p[1]][p[2]]=c
    eps=[1-dot(x,x) for x in s]
    ls=[math.sqrt(e/2) for e in eps];cs=[math.sqrt(1-e) for e in eps]
    t=[[[0.]*n for _ in range(n)] for _ in range(n)]
    for i,j,k in itertools.product(range(m),repeat=3):t[i][j][k]=s[i][j][k]
    for i in range(m):
        u=m+2*i;w=u+1
        for p in itertools.permutations((i,u,w)):t[p[0]][p[1]][p[2]]=ls[i]
        t[u][u][u]=t[w][w][w]=cs[i]
    actual=density(t);old=density(s);pred=[[0.]*n for _ in range(n)]
    for i,j in itertools.product(range(m),repeat=2):
        g=sum(eps[k]*sum(s[i][h][k]*s[j][h][k] for h in range(m)) for k in range(m))
        pred[i][j]=old[i][j]+g+(eps[i]-eps[i]**2/2 if i==j else 0)
    for i in range(m):
        u=m+2*i;w=u+1;l=ls[i];z=cs[i]
        for j in range(m):
            val=-z*l*l*s[j][i][i]-(2*z*l**3 if i==j else 0)
            pred[j][u]=pred[u][j]=pred[j][w]=pred[w][j]=val
        pred[u][u]=pred[w][w]=2*eps[i]-1.5*eps[i]**2
        pred[u][w]=pred[w][u]=-2*l**3*s[i][i][i]-z*z*l*l
    error=max(abs(actual[i][j]-pred[i][j]) for i,j in itertools.product(range(n),repeat=2))
    if error>1e-11:raise RuntimeError(('density block mismatch',error))
    return {'old_cubic_parameters':[a,c,d],'dimension':n,'all_density_blocks_max_error':error}
if __name__=='__main__':
    print(json.dumps({'status':'PASS_FINITE_FULL_DENSITY_BLOCK_DIAGNOSTICS_ONLY','cases':[run(.5,.2,.8),run(.8,.3,1),run(0,.5,.2)]},indent=2))
