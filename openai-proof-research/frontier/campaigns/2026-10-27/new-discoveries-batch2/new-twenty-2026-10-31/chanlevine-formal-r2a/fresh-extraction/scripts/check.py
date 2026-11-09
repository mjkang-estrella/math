"""Exact finite diagnostics; not a proof. No numerical complex arithmetic."""
from collections import defaultdict
from math import gcd, comb
import json

def counts(n,M):
    out=[[0]*n for _ in range(M+1)]
    # State: first rotor, first emptiness, last rotor, last emptiness, total, weight.
    d=defaultdict(int)
    for q in (0,1):
        for x in range(M+1): d[q,x==0,q,x==0,x,(1-q)%n]+=1
    for k in range(1,n):
        e=defaultdict(int)
        for (q0,z0,q,z,m,w),v in d.items():
            for r in (0,1):
                for x in range(M-m+1):
                    if q==1 and r==0 and z and x==0: continue
                    e[q0,z0,r,x==0,m+x,(w+k*x+1-r)%n]+=v
        d=e
    for (q0,z0,q,z,m,w),v in d.items():
        if q==1 and q0==0 and z and z0: continue
        if m: out[m][w]+=v
    return out

# Bivariate polynomials as dictionaries (t degree, z degree) -> integer.
def add(a,b):
    c=dict(a)
    for k,v in b.items(): c[k]=c.get(k,0)+v
    return {k:v for k,v in c.items() if v}
def neg(a): return {k:-v for k,v in a.items()}
def mul(a,b):
    c=defaultdict(int)
    for (i,j),v in a.items():
        for (k,l),w in b.items(): c[i+k,j+l]+=v*w
    return {k:v for k,v in c.items() if v}
def mm(A,B): return [[add(mul(A[i][0],B[0][j]),mul(A[i][1],B[1][j])) for j in range(2)] for i in range(2)]
O={}; I={(0,0):1}; Z={(0,1):1}
def mat(k):
    g={(0,0):1,(1,k):-1}
    return [[add(I,Z),neg(mul(Z,g))],[g,O]]
def trace(A): return add(A[0][0],A[1][1])
def prod(n):
    P=[[I,O],[O,I]]
    for k in range(n): P=mm(P,mat(k))
    return P
# Monic cyclotomic coefficients, computed by exact polynomial division.
def div(a,b):
    a=a[:]
    while a and not a[-1]: a.pop()
    q=[0]*max(1,len(a)-len(b)+1)
    while len(a)>=len(b):
        k=len(a)-len(b); v=a[-1]; q[k]=v
        for j,c in enumerate(b): a[j+k]-=v*c
        while a and not a[-1]: a.pop()
    return q,a
phis={}
for e in range(1,11):
    p=[-1]+[0]*(e-1)+[1]
    for d in range(1,e):
        if e%d==0: p,r=div(p,phis[d]); assert not r
    phis[e]=p

def rem(a,e):
    if not a:return []
    return div(a,phis[e])[1]
def coeff(p,t):
    a=[0]*(max([j for (i,j) in p if i==t],default=0)+1)
    for (i,j),v in p.items():
        if i==t:a[j]+=v
    return a

def norm(p,e):
    result={}
    for t in {i for i,j in p}:
        for j,v in enumerate(rem(coeff(p,t),e)):
            if v:result[t,j]=v
    return result

tests=0
for n in range(3,11):
    M=2*n; C=counts(n,M)
    for m in range(1,M+1):
        for i in range(n):
            assert C[m][i]==C[m][(i+m)%n]
            for u in range(n):
                if gcd(u,n)==1:assert C[m][i]==C[m][u*i%n]
            for j in range(n):
                if gcd(gcd(n,m),i)==gcd(gcd(n,m),j):
                    assert any((u*i+b*m)%n==j for u in range(n) if gcd(u,n)==1 for b in range(n))
        tests+=1
    P=prod(n); H=trace(P)
    # Independent matching expansion including wrap edges and corrected rotor factor.
    match={}
    for mask in range(1<<n):
        if any(mask>>k&1 and mask>>((k+1)%n)&1 for k in range(n)):continue
        edges=[k for k in range(n) if mask>>k&1]; r=len(edges)
        term={(0,r+j):(-1)**r*comb(n-2*r,j) for j in range(n-2*r+1)}
        for k in edges:
            for v in (k,(k+1)%n): term=mul(term,{(0,0):1,(1,v):-1})
        match=add(match,term)
    assert H==match
    for e in range(1,n+1):
        if n%e:continue
        E=prod(e); p=trace(E); q=0 if e%2 else 2*(-1)**(e//2)
        assert norm(p,e)=={k:v for k,v in {(0,0):2,(e,0):q}.items() if v}
        D=I
        for k in range(e):D=mul(D,{(0,0):1,(1,k):-1})
        assert norm(D,e)=={(0,0):1,(e,0):-1}
        det=add(mul(E[0][0],E[1][1]),neg(mul(E[0][1],E[1][0])))
        assert norm(det,e)=={(0,0):1,(e,0):-2,(2*e,0):1}
        Epower=[[I,O],[O,I]]
        for _ in range(n//e):Epower=mm(Epower,E)
        assert norm(trace(Epower),e)==norm(H,e)
        # Tr(P^r)/(1-t^e)^r - 2 versus literal CycleTest count.
        r=n//e
        for m in range(M+1):
            a=[]
            for b in range(m//e+1):
                v=comb(r+b-1,b)
                a=add({(0,j):x for j,x in enumerate(a)},
                      {(0,j):v*x for j,x in enumerate(coeff(H,m-e*b))})
                a=coeff(a,0)
            if m==0:a[0]-=2
            assert rem(a,e)==rem(C[m],e),(n,m,e)
    print(json.dumps({'n':n,'max_m':M,'status':'PASS'}),flush=True)
print(json.dumps({'cases':tests,'all_exact':True,'negative_control_wrong_rotor_factor':2*3**2!=3**2}))
