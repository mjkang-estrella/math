# Polynomial DP for d_n = deg(s: S_n -> S_n) = (1/n!) sum_y |s^{-1}(y)|^2.
# d_n = sum over pairs (B,B') of binary tree shapes on n nodes (postorder positions)
#       of prod_j 1/h_j, h_j = size of down-set of j in transitive closure of both tree orders.
# Block recursion (see SUMMARY): I[r][s][m] irreducible blocks, X block sequences, Y constrained.
import sys
from fractions import Fraction
from functools import lru_cache
sys.setrecursionlimit(100000)
MODE=sys.argv[2] if len(sys.argv)>2 else 'float'
one = Fraction(1) if MODE=='exact' else 1.0
zero = Fraction(0) if MODE=='exact' else 0.0
mu={0:1,1:2,2:1}
@lru_cache(maxsize=None)
def I(r,s,m):
    if r<1 or s<1 or m<1 or r>m or s>m: return zero
    if m==1: return one if (r==1 and s==1) else zero
    tot=zero
    for t in (0,1,2):
        for u in (0,1,2):
            R=r-1+t; S=s-1+u
            if t==0 and u==0: continue  # leaf in both: common boundary at m (m>1)
            v=Y(min(r,R),min(s,S),R,S,m-1)
            if v: tot+=mu[t]*mu[u]*v
    return tot/m
@lru_cache(maxsize=None)
def X(R,S,M):
    if M==0: return one if R==0 and S==0 else zero
    if R<1 or S<1 or R>M or S>M: return zero
    tot=zero
    for m1 in range(1,M+1):
        for r1 in range(1,min(R,m1)+1):
            for s1 in range(1,min(S,m1)+1):
                a=I(r1,s1,m1)
                if a:
                    b=X(R-r1,S-s1,M-m1)
                    if b: tot+=a*b
    return tot
@lru_cache(maxsize=None)
def Y(a,b,R,S,M):
    if M==0: return one if R==0 and S==0 else zero
    if R<1 or S<1 or R>M or S>M: return zero
    tot=I(R,S,M)
    for m1 in range(1,M):
        for r1 in range(1,min(R,m1)+1):
            for s1 in range(1,min(S,m1)+1):
                if r1>=a or s1>=b:
                    x=I(r1,s1,m1)
                    if x:
                        y=X(R-r1,S-s1,M-m1)
                        if y: tot+=x*y
    return tot
N=int(sys.argv[1]); prev=None
import math
for n in range(1,N+1):
    d=I(1,1,n)
    out=[n, (str(d*math.factorial(n)) if MODE=='exact' else ''), float(d), float(d)**(1/n), (float(d)/prev if prev else None)]
    print(*out, flush=True); prev=float(d)
