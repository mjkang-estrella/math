"""Deformed monotone Hurwitz numbers via the cut-and-join recursion (Coulter-Do-Moskovsky arXiv:2308.04015, Thm thm:cutjoin),
exact rational polynomials in t; tests real-rootedness (Sturm, exact) and interlacing (Con con:interlacing).
Usage: hurwitz.py G N_MAX MU_MAX"""
import sys, itertools, functools
from fractions import Fraction as F
import sympy as sp
sys.setrecursionlimit(100000)
t=sp.Symbol('t')
def padd(a,b):
    n=max(len(a),len(b)); return [ (a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pscale(a,c): return [x*c for x in a]
def pmul(a,b):
    if not a or not b: return []
    r=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def tmul(a): return [F(0)]+a  # t*a
@functools.lru_cache(maxsize=None)
def H(g,mu):  # mu: sorted tuple descending
    if g<0 or any(m<1 for m in mu) or not mu: return ()
    if g==0 and mu==(1,): return (F(1),)
    m1=mu[0]; S=list(mu[1:]); n=len(mu); acc=[]
    for i in range(len(S)):
        rest=S[:i]+S[i+1:]; acc=padd(acc,pscale(list(H(g,key((m1+S[i],)+tuple(rest)))),m1+S[i]))
    if m1>1:
        p=list(H(g,key((m1-1,)+tuple(S)))); acc=padd(acc,pscale(padd(tmul(p),pscale(p,-1)),m1-1))
    for a in range(1,m1):
        b=m1-a; inner=list(H(g-1,key((a,b)+tuple(S))))
        for mask in range(1<<len(S)):
            I1=tuple(S[j] for j in range(len(S)) if mask>>j&1); I2=tuple(S[j] for j in range(len(S)) if not mask>>j&1)
            for g1 in range(g+1):
                inner=padd(inner,pmul(list(H(g1,key((a,)+I1))),list(H(g-g1,key((b,)+I2)))))
        acc=padd(acc,pscale(inner,a*b))
    acc=pscale(acc,F(1,m1))
    while acc and acc[-1]==0: acc.pop()
    return tuple(acc)
def key(mu): return tuple(sorted(mu,reverse=True))
def topoly(c): return sp.Poly(sum(sp.Rational(x.numerator,x.denominator)*t**i for i,x in enumerate(c)),t)
def realrooted(P):
    return P.count_roots()==P.degree()  # exact Sturm count with multiplicity
import mpmath
mpmath.mp.dps=60
def mroots(P):
    c=[sp.Rational(x) for x in P.all_coeffs()]
    r=mpmath.polyroots([mpmath.mpf(x.p)/x.q for x in c],maxsteps=400,extraprec=400)
    return sorted(mpmath.re(z) for z in r)
NEAR=[]
def interlaces(P,Q):  # numeric (60 digits) weak interlacing; near-ties recorded for exact recheck
    if P.degree()==0 and Q.degree()==1: return True
    if Q.degree()!=P.degree()+1: return False
    a=mroots(P); b=mroots(Q); seq=[]
    for i in range(len(a)): seq+=[b[i],a[i]]
    seq.append(b[-1])
    for i in range(len(seq)-1):
        d=seq[i+1]-seq[i]
        if d < -mpmath.mpf(10)**-40: return False
        if abs(d) < mpmath.mpf(10)**-20 and abs(seq[i]) > mpmath.mpf(10)**-30: NEAR.append((str(P.as_expr()),str(Q.as_expr())))
    return True
if __name__=='__main__':
    # sanity: (mu+1) H(0,1;mu+1) = Narayana_mu
    for m in range(1,7):
        nar=[F(0)]+[F(sp.binomial(m,i)*sp.binomial(m,i-1),m) for i in range(1,m+1)]
        assert pscale(list(H(0,(m+1,))),m+1)==nar, m
    print('Narayana check OK', flush=True)
    G=int(sys.argv[1]); NMAX=int(sys.argv[2]); MUMAX=int(sys.argv[3]); checks=0; bad=[]
    from sympy.utilities.iterables import partitions
    for n in range(int(sys.argv[4]) if len(sys.argv)>4 else 1,NMAX+1):
        for tot in range(n,MUMAX+1):
            for p in partitions(tot,m=n):
                mu=[]; [mu.extend([k]*v) for k,v in p.items()]
                if len(mu)!=n: continue
                mu=key(mu); P=topoly(H(G,mu))
                if P.is_zero: continue
                if not realrooted(P): bad.append(('notrealrooted',G,mu)); print('NOT REAL-ROOTED',G,mu,flush=True); continue
                for i in set(range(n)):
                    nu=list(mu); nu[i]+=1; Q=topoly(H(G,key(nu))); checks+=1
                    if not realrooted(Q): continue
                    if not interlaces(P,Q): bad.append(('nointerlace',G,mu,key(nu))); print('NO INTERLACE',G,mu,key(nu),flush=True)
        print(f'g={G} n={n} |mu|<={MUMAX}: cumulative interlacing checks {checks}, failures {len(bad)}, near-ties {len(NEAR)}',flush=True)
