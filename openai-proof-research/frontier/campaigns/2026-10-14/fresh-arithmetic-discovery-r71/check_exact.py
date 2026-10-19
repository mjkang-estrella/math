#!/usr/bin/env python3
"""Exact rational finite diagnostics. The universal claims are proved in prose."""
from fractions import Fraction as F
from itertools import product
import json

def zero(n,m=None): return [[F(0) for _ in range(m or n)] for _ in range(n)]
def ident(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def add(a,b): return [[x+y for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,c): return [[x*c for x in r] for r in a]
def sub(a,b): return add(a,scale(b,-1))
def mm(a,b):
    bt=list(zip(*b))
    return [[sum((x*y for x,y in zip(r,s)),F(0)) for s in bt] for r in a]
def tr(a): return sum((a[i][i] for i in range(len(a))),F(0))
def norm2(a): return sum((x*x for r in a for x in r),F(0))
def outer(a,b): return [[x*y for y in b] for x in a]
def flat(a): return [x for r in a for x in r]
def pt(a,n):
    return [[a[i*n+l][k*n+j] for k,l in product(range(n),repeat=2)]
            for i,j in product(range(n),repeat=2)]
def ptr(a,n):
    return [[sum((a[i*n+j][k*n+j] for j in range(n)),F(0))
             for k in range(n)] for i in range(n)]

def simplex(m):
    n=m+1
    v=sub(ident(n),[[F(1,n)]*n for _ in range(n)])
    vecs=[flat(outer(v[i],v[i])) for i in range(n)]
    M=zero(n*n)
    P=zero(n*n)
    a2=F(m+1,m-1)
    for i in range(n):
        M=add(M,outer(vecs[i],vecs[i]))
        for j in range(n):
            P=add(P,scale(outer(vecs[i],vecs[j]),a2*v[i][j]))
    H=scale(outer(flat(v),flat(v)),F(1,m))
    Id=[[v[i][k]*v[j][l] for k,l in product(range(n),repeat=2)]
         for i,j in product(range(n),repeat=2)]
    Flip=[[v[i][l]*v[j][k] for k,l in product(range(n),repeat=2)]
           for i,j in product(range(n),repeat=2)]
    Sym=scale(add(Id,Flip),F(1,2)); Skew=scale(sub(Id,Flip),F(1,2))
    Z=sub(sub(Sym,H),P)
    assert mm(P,P)==P and tr(P)==m and ptr(P,n)==v
    assert scale(M,a2)==add(P,scale(H,F(m,m-1)))
    assert mm(Z,Z)==Z and tr(Z)==F((m-2)*(m+1),2)
    claimed=add(add(H,scale(P,F(m-2,m-1))),scale(sub(Skew,Z),F(1,m-1)))
    assert pt(P,n)==claimed
    assert norm2(sub(pt(P,n),P))==F(2*m,m-1)
    Q=add(scale(P,F(m-1,m)),H)
    assert Q==scale(M,F(m+1,m)) and ptr(Q,n)==v and pt(Q,n)==Q
    assert norm2(sub(Q,P))==1+F(1,m)
    return {'m':m,'negative_modes':int(tr(Z)),
            'negative_trace':str(tr(Z)/F(m-1)),
            'negative_squared_hs':str(tr(Z)/F((m-1)**2)),
            'short_repair_squared_hs':str(norm2(sub(Q,P)))}

def small(t):
    x=[[[F(1),t],[t,F(0)]],[[t,F(0)],[F(0),F(1)]]]
    B=add(mm(x[0],x[0]),mm(x[1],x[1]))
    beta=norm2(sub(B,ident(2)))
    C=norm2(sub(mm(x[0],x[1]),mm(x[1],x[0])))
    P=add(outer(flat(x[0]),flat(x[0])),outer(flat(x[1]),flat(x[1])))
    # Unnormalized skew vector removes sqrt(2); divide its quadratic form by two.
    h=[F(0),F(1),F(-1),F(0)]
    q=sum(h[i]*pt(P,2)[i][j]*h[j] for i in range(4) for j in range(4))/2
    assert beta==2*t*t+5*t**4 and C==2*(t-t*t)**2
    assert q==-t+t*t and norm2(sub(pt(P,2),P))==2*C
    assert beta+C==4*t*t-4*t**3+7*t**4

def main():
    # Five values independently determine the displayed degree-at-most-four
    # residual polynomials. The asymptotic obstruction is a symbolic prose proof.
    for t in [F(0),F(1,16),F(1,8),F(3,16),F(1,4)]:small(t)
    h=[F(0),F(1),F(-1),F(0)]
    W=pt(scale(outer(h,h),F(1,2)),2)
    assert mm(W,W)==scale(ident(4),F(1,4)) and tr(W)==1
    # Thus W has eigenvalues +/-1/2 and largest eigenvalue 1/2.
    results=[simplex(m) for m in [3,4,6]]
    print(json.dumps({'status':'EXACT_FINITE_DIAGNOSTICS_PASS',
      'simplex':results,'two_dimensional_polynomial_values':5,
      'partial_transpose_witness_square':'I/4',
      'full_target':'UNRESOLVED','universal_proof_location':'ppt-repair-obstructions.md'},sort_keys=True,indent=2))

if __name__=='__main__':main()
