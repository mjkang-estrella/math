# Exact Laplacian spectrum structure of power graph P(Z_n) via generalized join of cliques over divisor comparability.
import sys
from fractions import Fraction
def divisors(n): return [d for d in range(1,n+1) if n%d==0]
def phi(n):
    r=n;m=n;p=2
    while p*p<=m:
        if m%p==0:
            while m%p==0:m//=p
            r-=r//p
        p+=1
    if m>1:r-=r//m
    return r
def charpoly(M):
    # Berkowitz-free: Faddeev-LeVerrier with Fractions; returns coeffs c[0..k] of det(xI-M), highest first
    k=len(M); c=[Fraction(1)]; Mk=[[Fraction(0)]*k for _ in range(k)]
    I=[[Fraction(int(i==j)) for j in range(k)] for i in range(k)]
    A=[[Fraction(x) for x in row] for row in M]
    for m in range(1,k+1):
        # Mk = A*(Mk_prev + c_{m-1} I)
        B=[[Mk[i][j]+c[-1]*I[i][j] for j in range(k)] for i in range(k)]
        Mk=[[sum(A[i][t]*B[t][j] for t in range(k)) for j in range(k)] for i in range(k)]
        tr=sum(Mk[i][i] for i in range(k))
        c.append(-tr/m)
    return [int(x) for x in c]
def peval(c,x):
    v=0
    for a in c: v=v*x+a
    return v
def deflate(c,r):
    out=[c[0]]
    for a in c[1:-1]: out.append(a+out[-1]*r)
    return out
def int_roots(c,lo,hi):
    roots=[]
    for r in range(lo,hi+1):
        while len(c)>1 and peval(c,r)==0:
            roots.append(r); c=deflate(c,r)
    return roots,c
def spectrum(n):
    ds=divisors(n); k=len(ds); s=[phi(d) for d in ds]
    adj=[[i!=j and (ds[i]%ds[j]==0 or ds[j]%ds[i]==0) for j in range(k)] for i in range(k)]
    N=[sum(s[j] for j in range(k) if adj[i][j]) for i in range(k)]
    within=[]  # eigenvalue s_i+N_i (clique part) multiplicity s_i-1
    for i in range(k):
        if s[i]>1: within.append((s[i]+N[i], s[i]-1))
    Q=[[ (N[i] if i==j else (-s[j] if adj[i][j] else 0)) for j in range(k)] for i in range(k)]
    cp=charpoly(Q)
    roots,rest=int_roots(cp,0,n)
    return within,roots,rest
def factor(n):
    f={};p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def form3(n):
    f=factor(n); return len(f)==1 or (len(f)==2 and all(e==1 for e in f.values()))
lim=int(sys.argv[1])
for n in range(2,lim+1):
    within,roots,rest=spectrum(n)
    integral = len(rest)==1
    # algebraic connectivity: smallest nonzero eigenvalue among within and quotient roots (non-integer roots possible)
    cand=[e for e,_ in within]+[r for r in roots if r>0]
    nonint_deg=len(rest)-1
    # smallest nonzero eigenvalue: need numeric for nonint roots; estimate via sign changes on reals
    import math
    def realroots(c):
        # bisection on fine grid using float
        rs=[];prev=None;steps=20000
        for t in range(steps+1):
            x=n*t/steps*1.0
            v=0.0
            for a in c: v=v*x+a
            if prev is not None and (v==0 or (v>0)!=(prev[1]>0)): rs.append(x)
            prev=(x,v)
        return rs
    nr=realroots(rest) if nonint_deg>0 else []
    allpos=sorted([x for x in cand]+nr)
    a=allpos[0] if allpos else None
    a_is_int = (a in cand) and (not nr or min(nr)>a+1e-9)
    if integral!=form3(n) or a_is_int!=form3(n):
        print(n,factor(n),'integral',integral,'form3',form3(n),'a',a,'a_int',a_is_int,'nonint deg',nonint_deg,flush=True)
print('done',lim)
