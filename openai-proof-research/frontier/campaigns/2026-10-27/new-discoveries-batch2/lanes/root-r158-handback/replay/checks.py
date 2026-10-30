"""Exact bounded HHL/plethysm diagnostics, no conjectural inference."""
from pathlib import Path
from functools import lru_cache
from collections import Counter
from itertools import product
from math import factorial
import sympy as S
import json
L=Path(__file__).resolve().parent
q=S.Symbol('q')
@lru_cache(None)
def parts(n,m=None):
    if n==0:return ((),)
    if m is None:m=n
    return tuple((a,)+b for a in range(min(n,m),1-1,-1) for b in parts(n-a,a))
def z(p):
    a=1
    for r,c in Counter(p).items():a*=r**c*factorial(c)
    return a
def multiset_words(p):
    c=list(p);w=[]
    def go():
        if len(w)==sum(p):yield tuple(w);return
        for a in range(len(c)):
            if c[a]:
                c[a]-=1;w.append(a);yield from go();w.pop();c[a]+=1
    yield from go()
def stats(mu):
    cells=[(i,j) for i in reversed(range(len(mu))) for j in range(mu[i])]
    ix={c:i for i,c in enumerate(cells)}
    attacks=[(a,b) for a,(i,j) in enumerate(cells) for b,(h,l) in enumerate(cells) if (h==i and l>j) or (h==i-1 and l<j)]
    des=[(a,ix[i-1,j],mu[i]-j-1,sum(j<r for r in mu[i+1:])+1) for a,(i,j) in enumerate(cells) if (i-1,j) in ix]
    out=[]
    for p in parts(sum(mu)):
        co=Counter()
        for w in multiset_words(p):
            inv=sum(w[a]>w[b] for a,b in attacks)
            maj=0
            for a,b,arm,leg1 in des:
                if w[a]>w[b]:inv-=arm;maj+=leg1
            assert inv>=0
            co[inv,maj]+=1
        out.append(co)
    return out
def matrices(n):
    ps=parts(n);ind={p:i for i,p in enumerate(ps)}
    # p_nu -> m_lambda: assign each power-sum factor to a variable.
    A=S.zeros(len(ps));E=S.zeros(len(ps))
    for j,p in enumerate(ps):
        for i,lam in enumerate(ps):
            count=0
            for word in product(range(len(lam)),repeat=len(p)):
                v=[0]*len(lam)
                for r,a in zip(p,word):v[a]+=r
                count+=tuple(v)==lam
            A[i,j]=count
        d={():S.Integer(1)}
        for r in p:
            nxt={}
            for a,c in d.items():
                for b in parts(r):
                    v=tuple(sorted(a+b,reverse=True))
                    nxt[v]=nxt.get(v,0)+c*S.Rational((-1)**(r-len(b)),z(b))
            d=nxt
        for a,c in d.items():E[ind[a],j]=c
    return ps,A,A.inv(),E,E.inv()
def normalized(mu,k,ms=None):
    n=sum(mu);ps,A,Ai,E,Ei=matrices_cached(n)
    if ms is None:ms=stats(mu)
    H=S.Matrix([sum(c*q**(a+k*b) for (a,b),c in d.items()) for d in ms])
    ph=Ai*H
    ph=S.Matrix([S.expand(v*S.prod(q**(k*r)-1 for r in p)) for p,v in zip(ps,ph)])
    ec=Ei*ph
    ans=[]
    for v in ec:
        f,rem=S.div(S.Poly(S.expand(v),q),S.Poly((q-1)**n,q))
        assert rem.is_zero
        assert all(c.q==1 for c in f.all_coeffs())
        ans.append(f)
    return ps,ans
matrices_cached=lru_cache(None)(matrices)
records=[];controls=0
for n in range(1,8):
    for mu in parts(n):
        ms=stats(mu)
        for k in range(1,4):
            ps,ec=normalized(mu,k,ms)
            bad=[list(p) for p,f in zip(ps,ec) if any(c<0 for c in f.all_coeffs())]
            # Independent source Theorem6.1 coefficient, using original cells.
            exp=k*sum((i+1)*r for i,r in enumerate(mu))
            en=q**exp*(1-q**(-k*n))*S.prod(q**r-1 for r in range(1,mu[0]))
            en*=S.prod(q**j-q**(-k*i) for i,r in enumerate(mu) for j in range(r) if i>0)
            assert S.cancel(en/(q-1)**n-ec[ps.index((n,))].as_expr())==0
            controls+=1
            if mu==(1,)*n:
                expected=S.prod(sum(q**a for a in range(k*j)) for j in range(1,n+1))
                assert S.expand(ec[ps.index((n,))].as_expr()-expected)==0
            records.append(dict(mu=mu,k=k,coefficients=len(ec),negative=bad,max_degree=max(f.degree() for f in ec)))
        print('checked',mu,flush=True)
json.dump(dict(records=records,source_en_controls=controls,range='all partitions size1..7, k1..3',inference='bounded only'),(L/'checks.json').open('w'),indent=2)
# Schur positivity alone does not survive the proposed plethystic operation.
# s2=(p1^2+p2)/2, p2=e1^2-2e2.
obs=[]
for k in range(1,9):
    e2=-S.cancel((q**(2*k)-1)/(q-1)**2)
    assert e2.subs(q,2)<0
    obs.append(dict(k=k,e2_at_q2=str(e2.subs(q,2))))
json.dump(obs,(L/'schur-obstruction.json').open('w'),indent=2)
# A stronger obstruction: polynomial divisibility and the q=1 specialization
# still do not repair generic Schur positivity.
a=q-1;b=q*q-1
e11=S.cancel(((1+q*q)*a*a+(1-q*q)*b)/2/a**2)
e2=S.cancel((q*q-1)*b/a**2)
assert e11==-q and S.expand(e2-(q+1)**2)==0
# Independent orthogonal-triangular definition at nonsingular q=2,t=1/3.
orthogonal=0
examples=[]
for n in range(1,7):
    ps,A,Ai,E,Ei=matrices_cached(n)
    diag=S.diag(*[z(p)*S.prod((1-S.Integer(2)**r)/(1-S.Rational(1,3)**r) for r in p) for p in ps])
    basis=[]
    for j in reversed(range(len(ps))):
        v=Ai[:,j]
        for w in basis:v=v-w*((w.T*diag*v)[0]/(w.T*diag*w)[0])
        basis.append(v)
        mu=ps[j]
        c=S.prod(1-S.Integer(2)**(mu[i]-h-1)*S.Rational(1,3)**(sum(h<r for r in mu[i+1:])+1) for i,row in enumerate(mu) for h in range(row))
        J=c*v
        _,ec=normalized(mu,1)
        H=S.Matrix([sum(c*S.Integer(2)**a*S.Integer(3)**b for (a,b),c in d.items()) for d in stats(mu)])
        hp=Ai*H
        recovered=S.Matrix([v*S.prod(1-S.Rational(1,3)**r for r in p)*S.Rational(1,3)**sum(i*r for i,r in enumerate(mu)) for p,v in zip(ps,hp)])
        assert all(S.cancel(x)==0 for x in J-recovered)
        orthogonal+=1
        if mu==(3,2):examples=[dict(partition=p,coefficient=str(f.as_expr())) for p,f in zip(ps,ec)]
json.dump(dict(orthogonal_definition_controls=orthogonal,parameters='q=2,t=1/3',mu32_k1=examples,strong_obstruction=dict(input='s2+q^2*s11',output='-q*e11+(q+1)^2*e2',input_at_q1='p1^2',not_macdonald=True)),(L/'independent-controls.json').open('w'),indent=2)
print('PASS',len(records),'normalized functions;',controls,'source coefficient controls')
