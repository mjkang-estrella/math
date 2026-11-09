# Exact integer DP: P_n = #{(sigma,sigma') in S_n^2 : s(sigma)=s(sigma')} = n! d_n.
# Labelled versions: Ii(r,s,m)=m!*I, Xi=M!*X, Yi=M!*Y (see stack_deg_dp.py for the rational recursion).
import sys, math, json
from functools import lru_cache
sys.setrecursionlimit(100000)
mu={0:1,1:2,2:1}
C=[[math.comb(a,b) for b in range(201)] for a in range(201)]
@lru_cache(maxsize=None)
def I(r,s,m):
    if r<1 or s<1 or m<1 or r>m or s>m: return 0
    if m==1: return 1 if (r==1 and s==1) else 0
    tot=0
    for t in (0,1,2):
        for u in (0,1,2):
            if t==0 and u==0: continue
            R=r-1+t; S=s-1+u
            tot+=mu[t]*mu[u]*Y(min(r,R),min(s,S),R,S,m-1)
    return tot   # m! * (1/m) * (m-1)!^{-1}*Yi  => Ii = sum mu mu Yi
@lru_cache(maxsize=None)
def X(R,S,M):
    if M==0: return 1 if R==0 and S==0 else 0
    if R<1 or S<1 or R>M or S>M: return 0
    tot=0
    for m1 in range(1,M+1):
        cm=C[M][m1]
        for r1 in range(1,min(R,m1)+1):
            for s1 in range(1,min(S,m1)+1):
                a=I(r1,s1,m1)
                if a:
                    b=X(R-r1,S-s1,M-m1)
                    if b: tot+=cm*a*b
    return tot
@lru_cache(maxsize=None)
def Y(a,b,R,S,M):
    if M==0: return 1 if R==0 and S==0 else 0
    if R<1 or S<1 or R>M or S>M: return 0
    tot=I(R,S,M)
    for m1 in range(1,M):
        cm=C[M][m1]
        for r1 in range(1,min(R,m1)+1):
            for s1 in range(1,min(S,m1)+1):
                if r1>=a or s1>=b:
                    x=I(r1,s1,m1)
                    if x:
                        y=X(R-r1,S-s1,M-m1)
                        if y: tot+=cm*x*y
    return tot
N=int(sys.argv[1]); out={}
for n in range(1,N+1):
    out[n]=I(1,1,n); print(n,out[n],flush=True)
json.dump({str(k):str(v) for k,v in out.items()},open(sys.argv[2],'w'),indent=0)
