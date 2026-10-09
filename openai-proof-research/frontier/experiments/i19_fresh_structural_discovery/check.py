#!/usr/bin/env python3
"""Exact finite diagnostics, not a proof of any infinite-family conjecture."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
from math import factorial, comb
from pathlib import Path
import json
OUT=Path(__file__).resolve().parent

@lru_cache(None)
def parts(n,cap=None):
    if n==0:return ((),)
    cap=min(n,n if cap is None else cap)
    return tuple((a,)+b for a in range(cap,0,-1) for b in parts(n-a,a))
def cells(p):return {(i,j) for i,r in enumerate(p) for j in range(r)}
@lru_cache(None)
def rim(p,k):
    ans=[];A=cells(p)
    for q in parts(sum(p)-k):
        B=cells(q)
        if not B<=A:continue
        R=A-B
        if any({(i,j),(i+1,j),(i,j+1),(i+1,j+1)}<=R for i,j in R):continue
        seen={next(iter(R))}
        while True:
            z=seen|{(i+di,j+dj) for i,j in seen for di,dj in [(1,0),(-1,0),(0,1),(0,-1)] if (i+di,j+dj) in R}
            if z==seen:break
            seen=z
        if seen==R:ans.append((q,(-1)**(len({i for i,j in R})-1)))
    return tuple(ans)
@lru_cache(None)
def chi(p,mu):
    if not mu:return int(not p)
    return sum(s*chi(q,mu[1:]) for q,s in rim(p,mu[0]))
def zmu(mu):
    z=1
    for k,v in Counter(mu).items():z*=k**v*factorial(v)
    return z
def square_type(mu):return tuple(sorted([j//2 for j in mu if j%2==0 for _ in range(2)]+[j for j in mu if j%2],reverse=True))
@lru_cache(None)
def split(p):
    n=sum(p); ans={}
    for lam in parts(n):
        a=sum((Q(chi(lam,mu)*(chi(p,mu)**2+chi(p,square_type(mu))),2*zmu(mu)) for mu in parts(n)),Q())
        b=sum((Q(chi(lam,mu)*(chi(p,mu)**2-chi(p,square_type(mu))),2*zmu(mu)) for mu in parts(n)),Q())
        assert a.denominator==b.denominator==1 and a>=0 and b>=0
        ans[lam]=(int(a),int(b))
    d=chi(p,(1,)*n)
    assert sum(chi(l,(1,)*n)*v[0] for l,v in ans.items())==d*(d+1)//2
    assert sum(chi(l,(1,)*n)*v[1] for l,v in ans.items())==d*(d-1)//2
    return ans
@lru_cache(None)
def lr(lam,nu,eta):
    if sum(lam)!=sum(nu)+sum(eta) or not cells(nu)<=cells(lam):return 0
    skew=cells(lam)-cells(nu)
    if any(sum(j==c for i,j in skew)>len(eta) for c in range(lam[0])):return 0
    order=sorted(skew,key=lambda x:(x[0],-x[1]));fill={};counts=[0]*len(eta)
    def rec(k):
        if k==len(order):return 1
        i,j=order[k];ans=0
        for a in range(len(eta)):
            if counts[a]==eta[a]:continue
            if (i,j+1) in fill and a>fill[i,j+1]:continue
            if (i-1,j) in fill and a<=fill[i-1,j]:continue
            counts[a]+=1
            if all(counts[t]>=counts[t+1] for t in range(len(eta)-1)):
                fill[i,j]=a;ans+=rec(k+1);del fill[i,j]
            counts[a]-=1
        return ans
    return rec(0)
def horizontal(lam,nu,k):
    R=cells(lam)-cells(nu)
    return cells(nu)<=cells(lam) and len(R)==k and len({j for i,j in R})==k

def layer(B,kind):
    blocks=[]
    for k in sorted({b[0 if kind=='row' else 1] for b in B}):
        block=sorted([b for b in B if b[0 if kind=='row' else 1]==k],key=lambda x:x[1 if kind=='row' else 0]);blocks.append(block)
    choices=[]
    for bl in blocks:
        choices.append([(dict(zip(bl,p)),(-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))) for p in permutations(range(1,len(bl)+1))])
    ans={}
    for choiceset in product(*choices):
        d={};sg=1
        for dd,ss in choiceset:d.update(dd);sg*=ss
        ans[tuple(d[b] for b in B)]=sg
    return ans

def main():
    results={};band_checks=0
    for m in range(2,7):
        for lam,v in split((m,m-1)).items():
            expected=(int(len(lam)<=4 and sum(a%2 for a in lam)==1),int(len(lam)<=4 and sum(a%2 for a in lam)==3))
            assert v==expected;band_checks+=1
    results['band_character_checks']=band_checks
    lower={1:{(1,):(1,0)},2:split((2,1))};tables=[];coeffchecks=0
    for m in range(3,6):
        n=m*(m+1)//2;now={};actual=split(tuple(range(m,0,-1)))
        for lam in parts(n):
            by1=[sum(v[ep] for nu,v in lower[m-1].items() if horizontal(lam,nu,m)) for ep in (0,1)]
            by2=[0,0]
            for nu,v in lower[m-2].items():
                for eta in parts(2*m-1):
                    if len(eta)>4:continue
                    c=lr(lam,nu,eta)
                    if c:
                        band_eps=(sum(a%2 for a in eta)-1)//2
                        for ep in (0,1):by2[ep]+=c*v[ep^band_eps]
            now[lam]=tuple(max(a,b) for a,b in zip(by1,by2))
            assert all(now[lam][ep]<=actual[lam][ep] for ep in (0,1));coeffchecks+=2
        # Source cyclic support plus the known unique trivial/sign constituents.
        now[(n,)]=(max(1,now[(n,)][0]),now[(n,)][1])
        sign_eps=int(m%4==2);tmp=list(now[(1,)*n]);tmp[sign_eps]=max(1,tmp[sign_eps]);now[(1,)*n]=tuple(tmp)
        lower[m]=now
        tables.append(dict(m=m,partitions=len(now),positive_lower_symmetric=sum(v[0]>0 for v in now.values()),positive_lower_exterior=sum(v[1]>0 for v in now.values()),actual_symmetric=sum(v[0]>0 for v in actual.values()),actual_exterior=sum(v[1]>0 for v in actual.values()),rows=[dict(partition=list(l),lower=list(now[l]),actual=list(actual[l])) for l in parts(n)]))
    results['signed_lower_bound_checks']=coeffchecks;results['signed_tables']=tables
    # Independent character orthogonality through S_7 validates the MN routine.
    orth=0
    for n in range(1,8):
        for a in parts(n):
            for b in parts(n):
                assert sum((Q(chi(a,mu)*chi(b,mu),zmu(mu)) for mu in parts(n)),Q())==int(a==b);orth+=1
    results['character_orthogonality_checks']=orth
    tensorcases=[]
    for m in range(2,5):
        B=tuple((i,j) for i in range(1,m+1) for j in range(1,m+2-i));index={b:i for i,b in enumerate(B)}
        R=layer(B,'row');C=layer(B,'col');tr=lambda w:tuple(w[index[j,i]] for i,j in B)
        assert {tr(w):a for w,a in R.items()}==C
        for s in (1,2):
            h=m-s
            if h<1:continue
            D=tuple(b for b in B if sum(b)<=h+1);F=tuple(b for b in B if b not in D)
            rh,ch=layer(D,'row'),layer(D,'col');rf,cf=layer(F,'row'),layer(F,'col')
            expected={}
            for (a,aa),(b,bb),(c,cc),(d,dd) in product(rh.items(),ch.items(),rf.items(),cf.items()):
                x=dict(zip(D,(v+s for v in a)));x.update(zip(F,c));y=dict(zip(D,(v+s for v in b)));y.update(zip(F,d));expected[tuple(x[v] for v in B),tuple(y[v] for v in B)]=aa*bb*cc*dd
            got={(a,b):aa*bb for a,aa in R.items() for b,bb in C.items() if all((x>s)==(y>s) for x,y in zip(a,b))}
            assert got==expected
            assert {(b,a):v for (a,b),v in got.items()}=={(tr(a),tr(b)):v for (a,b),v in got.items()}
            tensorcases.append(dict(m=m,s=s,unprojected_words=len(R)*len(C),retained_words=len(got)))
    results['tensor_projection_cases']=tensorcases
    # Exact positive-weight complete-host obstruction.
    def matchings(v):
        if not v:return [frozenset()]
        a=v[0];out=[]
        for b in v[1:]:
            for z in matchings([x for x in v if x not in (a,b)]):out.append(z|{tuple(sorted((a,b)))})
        return out
    states=matchings(list(range(6)));cycle={tuple(sorted((i,(i+1)%6))) for i in range(6)}
    exp={M:sum(e not in cycle for e in M) for M in states};poly=Counter(exp.values());M=next(M for M in states if exp[M]==0)
    exits=Counter(exp[N] for N in states if len(M-N)==2)
    assert poly[0]==2 and exits[0]==0
    numerical=[]
    for L in range(1,13):
        delta=Q(1,2**L);Z=sum(delta**exp[N] for N in states);pi=1/Z
        q=sum(delta**exp[N]/(12*comb(6,4)) for N in states if len(M-N)==2)
        assert pi<=Q(1,2) and q<=delta/2
        t=2**(L-1)-1
        assert 1-t*q-pi>Q(1,4)
        numerical.append(dict(L=L,pi=str(pi),exit_probability=str(q),certified_time=t))
    results['weighted_cycle']={'state_count':len(states),'partition_polynomial':dict(sorted(poly.items())),'exit_exponents':dict(sorted(exits.items())),'checks':numerical}
    # Source triangular chart, D=3, with rational times in prescribed order.
    t=[Q(1),Q(3,2),Q(2),Q(9,4),Q(11,4),Q(3)]
    def om(i,j):return (1 if i>j else -1) if i!=j and abs(t[i]-t[j])<1 else 0
    B=[[om(i+1,j+1)-om(i+1,j)-om(i,j+1)+om(i,j) for j in range(5)]for i in range(5)]
    assert B[0][3]>0 and B[3][1]>0 and B[1][0]>0
    results['root_quiver']={'times':[str(x) for x in t],'matrix':B,'directed_cycle_zero_based':[0,3,1,0]}
    # Formal e-positive and Schur-Lefschetz countermodel.
    e2=[1,0,1];e11=[0,1,0];s11=[a+b for a,b in zip(e2,e11)];s2=e11
    assert s11==[1,1,1] and s2==[0,1,0] and e2[1]<e2[0]
    results['formal_unimodality_countermodel']={'e2':e2,'e11':e11,'s11':s11,'s2':s2}
    results['status']='all assertions passed; finite diagnostics only'
    return results
if __name__=='__main__':
    r=main();(OUT/'results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['signed_tables']},indent=2))
