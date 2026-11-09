#!/usr/bin/env python3
# Original code, MIT. Bounded exact diagnostic, not a proof or review.
from functools import lru_cache
from fractions import Fraction as F
from math import factorial,prod,sqrt,pi
from collections import Counter
import json

def parts(n,cap=None):
    if not n:
        yield (); return
    for a in range(min(n,n if cap is None else cap),1-1,-1):
        for b in parts(n-a,a): yield (a,)+b

def dim(lam):
    h=prod(lam[i]-j+sum(a>j for a in lam[i+1:]) for i in range(len(lam)) for j in range(lam[i]))
    return factorial(sum(lam))//h

@lru_cache(None)
def char(lam,cyc):
    if not cyc:return int(not lam)
    k=cyc[0];L=len(lam);beads=tuple(lam[i]+L-1-i for i in range(L));bs=set(beads);ans=0
    for b in beads:
        a=b-k
        if a<0 or a in bs:continue
        ht=sum(a<c<b for c in beads)
        new=sorted((bs-{b})|{a},reverse=True)
        nu=tuple(v-(L-1-i) for i,v in enumerate(new) if v-(L-1-i)>0)
        ans+=(-1)**ht*char(nu,cyc[1:])
    return ans

def z(cyc):return prod(k**v*factorial(v) for k,v in Counter(cyc).items())

def run():
    rows=[]
    for m in range(2,7):
        n=m*(m+1)//2;rho=tuple(range(m,0,-1));d=dim(rho);ps=list(parts(n));cs=[char(rho,c) for c in ps]
        assert char(rho,(1,)*n)==d
        assert sum(F(v*v,z(c)) for c,v in zip(ps,cs))==1
        assert all(v==0 for c,v in zip(ps,cs) if any(k%2==0 for k in c))
        assert F(char(rho,(3,)+(1,)*(n-3)),d)==-F(1,2*(n-2))
        chi=sum(F(factorial(n),z(c))*F(v,d)**4 for c,v in zip(ps,cs) if c!=(1,)*n)
        lead=F(n*(n-1),48*(n-2)**3);res=chi-lead;assert res>=0
        row=dict(m=m,n=n,classes=len(ps),dimension=d,chi_square=str(chi),three_cycle_term=str(lead),tail=str(res),scaled_tail_n2=float(res*n*n),scaled_chi_n=float(chi*n))
        if m<=5:
            mu=[];pl=[];x3=[]
            for lam in ps:
                dl=dim(lam);g=sum(F(v*v*char(lam,c),z(c)) for c,v in zip(ps,cs))
                assert g.denominator==1 and g>=0
                mu.append(F(g*dl,d*d));pl.append(F(dl*dl,factorial(n)))
                x3.append(F(char(lam,(3,)+(1,)*(n-3)),dl))
            assert sum(mu)==sum(pl)==1
            assert sum((u-p)**2/p for u,p in zip(mu,pl))==chi
            # Leading likelihood term is |C3| r_rho(3)^2 r_lambda(3).
            c3=F(n*(n-1)*(n-2),3)
            rem=sum(p*(u/p-1-c3*F(1,4*(n-2)**2)*x)**2 for u,p,x in zip(mu,pl,x3))
            assert rem==res
            tv=sum(abs(u-p) for u,p in zip(mu,pl))/2
            row.update(tv=str(tv),sqrt_n_tv=float(tv)*sqrt(n),limit_constant=1/(4*sqrt(6*pi)),likelihood_residual_verified=True)
        rows.append(row)
        char.cache_clear()
    return dict(status='FINITE_EXACT_DIAGNOSTIC_ONLY',scope='m=2..6 character rows; m=2..5 full decomposition',rows=rows)
if __name__=='__main__':print(json.dumps(run(),indent=2))
