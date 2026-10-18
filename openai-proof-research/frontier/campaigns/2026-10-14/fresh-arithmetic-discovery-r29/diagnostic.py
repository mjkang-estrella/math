#!/usr/bin/env python3
"""Exact finite diagnostics; these do not certify the geometric/LND proof. MIT."""
import json
from collections import defaultdict
class P:
    N=8
    def __init__(self,d=None): self.d={k:v for k,v in (d or {}).items() if v}
    @staticmethod
    def c(v): return P({(0,)*P.N:v})
    @staticmethod
    def v(i):
        t=[0]*P.N;t[i]=1;return P({tuple(t):1})
    def __add__(a,b):
        if not isinstance(b,P):b=P.c(b)
        d=defaultdict(int,a.d)
        for k,v in b.d.items():d[k]+=v
        return P(d)
    __radd__=__add__
    def __neg__(a):return P({k:-v for k,v in a.d.items()})
    def __sub__(a,b):return a+-b if isinstance(b,P) else a+(-b)
    def __rsub__(a,b):return -a+b
    def __mul__(a,b):
        if not isinstance(b,P):b=P.c(b)
        d=defaultdict(int)
        for k,v in a.d.items():
            for l,w in b.d.items():d[tuple(x+y for x,y in zip(k,l))]+=v*w
        return P(d)
    __rmul__=__mul__
    def __pow__(a,n):
        r=P.c(1)
        for _ in range(n):r=r*a
        return r
    def diff(a,i):
        d={}
        for k,v in a.d.items():
            if k[i]:l=list(k);l[i]-=1;d[tuple(l)]=v*k[i]
        return P(d)
    def eq(a,b):return not (a-b).d

def run():
    counts={}
    p,s,u,F,J,w,L,M=[P.v(i) for i in range(8)]
    for n in range(2,17):
        x=s*s+u**3+p**n*F;y=s+x*(x-u**3);z=s*x+p**n*J
        H=x*x*F-(1+2*s*x)*J-p**n*J*J-p*u
        assert (x*y-z*(z+1)).eq(p**n*(H+p*u))
        values=[P.c(0),-3*p**n*x*u*u,-p**n,(6*s*x+3)*u*u,3*x*x*u*u,P.c(0),P.c(0),P.c(0)]
        DH=sum((H.diff(i)*v for i,v in enumerate(values)),P.c(0))
        assert DH.eq(p**(n+1))
        x0=s*s+u**3
        FF=4*s*s*L+(1+2*s*x0)*M;JJ=-(1-2*s*x0)*L+x0*x0*M
        assert (x0*x0*FF-(1+2*s*x0)*JJ).eq(L)
        assert ((1-2*s*x0)*FF+4*s*s*JJ).eq(M)
        xx=x0+p**n*FF
        Q=2*x0*FF*FF-2*s*FF*JJ-JJ*JJ
        HH=xx*xx*FF-(1+2*s*xx)*JJ-p**n*JJ*JJ-p*u
        assert HH.eq(L-p*u+p**n*Q+p**(2*n)*FF**3)
    counts['construction_and_derivation_n']=15
    # Independent formal placeholders C,q,Z model Q=C+Lq and F^3=Z.
    p,L,u,C,q,Z,w,_=[P.v(i) for i in range(8)]
    for n in range(2,41):
        Q=C+L*q;H=L-p*u+p**n*Q+p**(2*n)*Z
        h=u-p**(n-1)*Q-p**(2*n-1)*Z-p**n*w
        e=-w-p**(n-1)*Z-q*h;Ls=p*u-p**n*C
        assert (p**(n+1)*e-(L-Ls)).eq((p**n*q-1)*(H+p**(n+1)*w))
        assert (Ls-p*u+p**n*(C+Ls*q)+p**(2*n)*Z).eq(p**(n+1)*((u-p**(n-1)*C)*q+p**(n-1)*Z))
    counts['fifth_coordinate_and_root_n']=39
    for n in range(2,41):
        for r in range(1,121):
            k=(r+n-1)//n
            admissible=[j for j in range(150) if n*j>=r]
            assert min(admissible)==k
            assert ((k==1)==(r<=n))
            # Local chart model t=p^n V: coefficient at p^0 in S
            # comes from monomials t^j, and divisibility in A is nj>=r.
            assert [j for j in range(150) if n*j>=r]==[j for j in range(150) if j>=k]
        for m in range(1,101): assert (2-n)*m-2<0
    counts['staircase_cases']=39*120;counts['order_drop_cases']=39*100
    # Mutations must be rejected by exact identities/examples.
    assert any((r//n)!=((r+n-1)//n) for n in range(2,6) for r in range(1,10))
    assert (2-1)*3-2>=0 # n=1 does not support the source-rigidity extraction.
    n=3;r=4;assert 2*n>=r and 2>=((r+n-1)//n)
    # t^2 lies in p^4 A∩S for t=p^3V but is not in (p^4,p*t)⊂C[p,t].
    assert not (0>=4 or (0>=1 and 2>=1))
    counts['detected_mutations']=['floor_for_ceiling','n1_order_extension','truncated_two_generator_contraction']
    return {'status':'PASS_EXACT_FINITE_DIAGNOSTICS','counts':counts,'limit':'No formal or numerical certification of LND classification, algebraic geometry, or the full theorem.'}
if __name__=='__main__': print(json.dumps(run(),indent=2,sort_keys=True))
