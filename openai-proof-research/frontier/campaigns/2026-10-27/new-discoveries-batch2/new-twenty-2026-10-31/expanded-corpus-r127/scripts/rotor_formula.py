# Closed formula for r(C_{n,m,i}) derived in outputs/338887-proof.md; checked against outputs/rotor-counts.jsonl (exact DP).
import json, math, sys, pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def mobius(n):
    r=1; p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            if n%p==0: return 0
            r=-r
        p+=1
    return -r if n>1 else r
def phi(n): return sum(1 for a in range(1,n+1) if math.gcd(a,n)==1)
def ramanujan(e,i):
    g=math.gcd(e,i); return mobius(e//g)*phi(e)//phi(e//g)
def q(e): return 0 if e%2 else (2 if e%4==0 else -2)
def W(n,m,e):
    if m%e: return 0
    r=n//e; L=m//e+1
    tau=[2]+[2+q(e)]*(L-1)          # (2+qT)/(1-T) = 2 + (2+q) sum_{j>=1} T^j
    mul=lambda a,b:[sum(a[i]*b[j-i] for i in range(j+1)) for j in range(L)]
    V0=[2]+[0]*(L-1); V1=tau[:]
    if r==0: V=V0
    else:
        for _ in range(r-1): V0,V1=V1,[x-y for x,y in zip(mul(tau,V1),V0)]
        V=V1
    return V[m//e]-(2 if m//e==0 else 0)
from functools import lru_cache
@lru_cache(None)
def series(n,e,L):
    r=n//e
    tau=[2]+[2+q(e)]*(L-1)
    mul=lambda a,b:[sum(a[i]*b[j-i] for i in range(j+1)) for j in range(L)]
    V0=[2]+[0]*(L-1); V1=tau[:]
    for _ in range(r-1): V0,V1=V1,[x-y for x,y in zip(mul(tau,V1),V0)]
    return V1
def Wc(n,m,e):
    if m%e: return 0
    L=(3*n)//e+2; return series(n,e,L)[m//e]-(2 if m==0 else 0)
def N(n,m,i,cache={}):
    d=math.gcd(n,m)
    if (n,m) not in cache: cache[(n,m)]={e:Wc(n,m,e) for e in range(1,d+1) if d%e==0}
    s=sum(w*ramanujan(e,i) for e,w in cache[(n,m)].items())
    assert s%n==0; return s//n
bad=0; tot=0
for line in open(D/'outputs/rotor-counts.jsonl'):
    o=json.loads(line); n,m=o['n'],o['m']; r=[int(x) for x in o['r']]
    pred=[N(n,m,i) for i in range(n)]; tot+=1
    if pred!=r: bad+=1; print('MISMATCH',n,m,r[:4],pred[:4])
print(json.dumps({'rows_checked':tot,'mismatches':bad}))
