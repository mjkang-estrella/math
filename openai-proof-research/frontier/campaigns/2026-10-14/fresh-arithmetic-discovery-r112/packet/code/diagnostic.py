"""Exact finite theta-diagram diagnostics; not a mathematical gate."""
from fractions import Fraction as F
from math import isqrt
import json

def floor_quad(a,b,r):
    # floor(a*sqrt(r)+b), a>=0, b rational; exact integer inequalities.
    assert a>=0
    v=isqrt(a*a*r)+b.numerator//b.denominator
    def le(x):
        c=F(x)-b
        return c<=0 or c*c<=a*a*r
    while le(v+1):v+=1
    while not le(v):v-=1
    return v

def diagram(r,d,m,delta=F(1,1000)):
    assert d>3*m and isqrt(r)**2!=r and 0<delta<F(1,2)
    h=3*(d-3*m);S=[]
    for j in range(d//3+1):
        n=h if j<=m else 3*(d-3*j)
        if n==0:S.append((j,0));continue
        a=d-3*j
        b=-3*a-F(h if j<=m else n,9)*delta
        u=floor_quad(a,b,r)
        S.extend((j,k) for k in range(u+1,u+n+1))
    assert len(S)==(d+2)*(d+1)//2-9*m*(m+1)//2
    return S

def rank_mod(A,p=1000003):
    a=[[v%p for v in row] for row in A];n=len(a);c=len(a[0]) if n else 0;i=0
    for j in range(c):
        k=next((k for k in range(i,n) if a[k][j]),None)
        if k is None:continue
        a[i],a[k]=a[k],a[i];inv=pow(a[i][j],-1,p)
        a[i][j:]=[(v*inv)%p for v in a[i][j:]]
        for k in range(i+1,n):
            z=a[k][j]
            if z:a[k][j:]=[(x-z*y)%p for x,y in zip(a[k][j:],a[i][j:])]
        i+=1
        if i==n:break
    return i

def matrix(r,d,m,delta=F(1,1000)):
    S=diagram(r,d,m,delta);q=r-9
    I=[(ell,b) for b in range(m) for ell in range(q*(m-b))]
    return S,I,[[k**ell*j**b for j,k in S] for ell,b in I]

if __name__=='__main__':
    cases=[]
    for r,d,m in [(10,19,6),(10,38,12),(10,57,18),(10,22,7),(11,10,3),(12,7,2),(13,11,3),(14,15,4),(15,4,1)]:
        S,I,A=matrix(r,d,m);rank=rank_mod(A);chi=(d+2)*(d+1)//2-r*m*(m+1)//2
        x=dict(r=r,d=d,m=m,chi=chi,rows=len(I),columns=len(S),rank_mod_1000003=rank,full_rank_witness=rank==min(len(I),len(S)))
        cases.append(x);print(x)
    from pathlib import Path
    (Path(__file__).resolve().parents[1]/'scratch/diagnostic.json').write_text(json.dumps(cases,indent=2))
