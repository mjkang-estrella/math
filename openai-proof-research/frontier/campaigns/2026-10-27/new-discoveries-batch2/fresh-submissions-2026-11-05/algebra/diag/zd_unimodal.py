# Exact independence polynomial of zero-divisor graph Gamma(Z_n) via divisor-class compression.
import sys, math
from functools import lru_cache
def divisors(n):
    return sorted(d for d in range(1,n+1) if n%d==0)
def totient(n):
    r=n; m=n; p=2
    while p*p<=m:
        if m%p==0:
            while m%p==0: m//=p
            r-=r//p
        p+=1
    if m>1: r-=r//m
    return r
from math import comb
def poly_add(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def poly_mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def indep_poly(n):
    ds=[d for d in divisors(n) if d!=1 and d!=n]
    w={}
    for d in ds:
        s=int(totient(n//d))
        if (d*d)%n==0: w[d]=[0,s]
        else: w[d]=[0]+[comb(s,k) for k in range(1,s+1)]
    k=len(ds); adj=[0]*k
    for i in range(k):
        for j in range(k):
            if i!=j and (ds[i]*ds[j])%n==0: adj[i]|=1<<j
    @lru_cache(None)
    def rec(mask):
        if mask==0: return (1,)
        i=(mask&-mask).bit_length()-1
        a=rec(mask&~(1<<i))
        b=poly_mul(w[ds[i]],list(rec(mask&~(1<<i)&~adj[i])))
        return tuple(poly_add(list(a),b))
    return list(rec((1<<k)-1))
def unimodal(c):
    i=0
    while i+1<len(c) and c[i]<=c[i+1]: i+=1
    while i+1<len(c) and c[i]>=c[i+1]: i+=1
    return i==len(c)-1
def lc(c):
    return all(c[i]*c[i]>=c[i-1]*c[i+1] for i in range(1,len(c)-1))
N=int(sys.argv[1]); bad=[]; nlc=[]
for n in range(4,N+1):
    if len(divisors(n))>40: 
        continue
    c=indep_poly(n)
    if not unimodal(c): bad.append(n); print('NONUNIMODAL',n,c[:60],flush=True)
    if not lc(c): nlc.append(n)
print('checked up to',N,'nonunimodal',bad,'non-LC count',len(nlc),nlc[:30])
