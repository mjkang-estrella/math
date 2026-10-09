"""Embedding test for rational quadratic spaces T (sig (2,t-2)) into
V_P = U^2 + <-1>^4 (sig (2,6)), the corpus K3 quadratic locus.

Criterion (proved in the report, Theorem A):
  t<=5: always embeds.
  t=6, delta=det T>0: embeds iff c_p(T) = 1 for every prime p split in Q(sqrt(-delta)).
  t=7, delta'=det T<0: embeds iff c_p(T) = c_p(V_P)*(delta',delta')_p for all primes p.
  t=8: iff T ~= V_P.
This script (a) implements Hilbert symbols, (b) cross-checks the t=6 criterion against a
brute-force search for a binary complement N=<x, x*delta> with T+N ~= V_P (local invariants),
and (c) prints explicit uncovered examples.  Run: python3 -I vp_embedding.py
"""
from fractions import Fraction
import itertools, math

def vp(n,p):
    v=0
    while n%p==0: n//=p; v+=1
    return v,n
def legendre(a,p):
    a%=p
    if a==0: return 0
    r=pow(a,(p-1)//2,p)
    return -1 if r==p-1 else r
def hilbert(a,b,p):
    """Hilbert symbol (a,b)_p for nonzero integers a,b; p prime or 'inf'."""
    if p=='inf':
        return -1 if (a<0 and b<0) else 1
    al,u=vp(a,p); be,w=vp(b,p)
    if p!=2:
        e=(p-1)//2
        s=(-1)**((al*be*e)%2)
        return s*legendre(u,p)**be*legendre(w,p)**al
    eps=lambda x: ((x-1)//2)%2
    om=lambda x: ((x*x-1)//8)%2
    expo=(eps(u)*eps(w)+al*om(w)+be*om(u))%2
    return -1 if expo else 1
def hasse(diag,p):
    c=1
    for i in range(len(diag)):
        for j in range(i+1,len(diag)):
            c*=hilbert(diag[i],diag[j],p)
    return c
def sqfree(n):
    s=1 if n>0 else -1; n=abs(n); r=1; d=2
    while d*d<=n:
        while n%(d*d)==0: n//=d*d
        d+=1
    return s*n
def is_local_square(a,p):
    if p=='inf': return a>0
    v,u=vp(a,p)
    if v%2: return False
    if p==2: return u%8==1
    return legendre(u,p)==1
def primes_upto(n):
    return [q for q in range(2,n+1) if all(q%r for r in range(2,int(q**0.5)+1))]
VP=[1,-1,1,-1,-1,-1,-1,-1]
def relevant_primes(diag):
    ps={2}
    for a in diag:
        n=abs(a); d=2
        while d*d<=n:
            while n%d==0: ps.add(d); n//=d
            d+=1
        if n>1: ps.add(n)
    return sorted(ps)
def criterion6(T):
    delta=math.prod(T); assert delta>0
    bad=[]
    for p in relevant_primes(T):
        if is_local_square(-delta,p) and hasse(T,p)!=1: bad.append(p)
    return bad  # empty => embeds
def brute6(T,X=200):
    """Search x<0, |x|<=X with T+<x,x*delta> ~= V_P via local invariants at relevant places."""
    delta=math.prod(T)
    for x in range(-1,-X-1,-1):
        N=[x,x*delta]
        ps=set(relevant_primes(T+N))|{2}
        if all(hasse(T+N,p)==hasse(VP,p) for p in ps) and hasse(T+N,'inf')==hasse(VP,'inf'):
            # det: prod(T+N)=x^2 delta^2 square, det V_P=1 ok; signature ok since x<0
            return x
    return None
# cross-check
import random
random.seed(1)
agree=0; tested=0; uncovered=[]
pool=[1,2,3,5,6,7,10,11,13,14,15,17,19,21,22,23]
for _ in range(400):
    pos=[random.choice(pool) for _ in range(2)]
    neg=[-random.choice(pool) for _ in range(4)]
    T=pos+neg
    bad=criterion6(T)
    b=brute6(T, X=2000)
    tested+=1
    ok=(not bad)==(b is not None)
    agree+=ok
    if not ok: print("MISMATCH",T,bad,b)
    if bad and len(uncovered)<6: uncovered.append((T,bad,sqfree(-math.prod(T))))
print(f"criterion vs brute force agree on {agree}/{tested}")
for T,bad,K in uncovered:
    print("uncovered rank-6 example T =",T," K=Q(sqrt(%d))"%K," failing split primes:",bad)
