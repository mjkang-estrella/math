#!/usr/bin/env python3
"""MIT. Exact finite arithmetic checks, not a mathematical proof."""
from fractions import Fraction as F
import json, random


def normalize(mu, heights):
    if sum(mu)<=1:
        return list(mu), None
    for count in range(len(mu)+1):
        order=sorted(range(len(mu)), key=lambda i: heights[i], reverse=True)
        sat=set(order[:count]); rest=set(order[count:])
        top=1-sum(mu[i] for i in sat)
        bot=sum(mu[i]*heights[i] for i in rest)
        if bot<=0 or top<=0: continue
        c=top/bot
        if all(c*heights[i]>=1 for i in sat) and all(c*heights[i]<=1 for i in rest):
            out=[mu[i]*min(F(1),c*heights[i]) for i in range(len(mu))]
            assert sum(out)==1
            return out,c
    raise AssertionError('normalization parameter not found')


def cut(mu, parent):
    q=list(mu)
    for i in range(len(mu)-1,-1,-1):
        if parent[i]>=0:q[parent[i]]+=q[i]
    return q


def norm(mu, parent, weights):
    return sum(w*abs(x) for w,x in zip(weights,cut(mu,parent)))


def diff(a,b):return [x-y for x,y in zip(a,b)]


def main():
    rng=random.Random(33242)
    maximum=F(0); cases=0; mixed=0; fixed=0
    for n in range(1,9):
        for tree in range(8):
            parent=[rng.randrange(-1,i) for i in range(n)]
            weights=[F(rng.randrange(1,12),rng.randrange(1,8)) for i in range(n)]
            height=[]
            for i in range(n):height.append(weights[i]+(height[parent[i]] if parent[i]>=0 else 0))
            laws=[]
            for j in range(20):
                m=[F(rng.randrange(0,9),rng.randrange(1,10)) for _ in range(n)]
                if j%3==0 and sum(m)>0:m=[x/(2*sum(m)) for x in m]
                laws.append(m)
            for a,b in zip(laws,laws[1:]):
                ra,ca=normalize(a,height); rb,cb=normalize(b,height)
                assert sum(ra)<=1 and sum(rb)<=1
                if ca is None:assert ra==a; fixed+=1
                if cb is None:assert rb==b; fixed+=1
                mixed+=int((ca is None)!=(cb is None))
                d=norm(diff(a,b),parent,weights)
                e=norm(diff(ra,rb),parent,weights)
                assert e<=3*d
                if d:maximum=max(maximum,e/d)
                cases+=1
    # Nearby mixed-boundary data catch a false 1-Lipschitz strengthening.
    near_a=[F(0),F(1)]; near_b=[F(1,10),F(1)]
    near_h=[F(1,2),F(1)]
    near_ra,_=normalize(near_a,near_h); near_rb,_=normalize(near_b,near_h)
    near_ratio=norm(diff(near_ra,near_rb),[-1,-1],near_h)/norm(diff(near_a,near_b),[-1,-1],near_h)
    assert near_ratio==F(10,7) and near_ratio>1 and near_ratio<=3
    maximum=max(maximum,near_ratio)
    # Naive proportional normalization is a genuinely failing alternative.
    eps=F(1,1000); delta=F(1,10)
    a=[F(0),F(1)]; b=[delta,F(1)]
    naive_a=a; naive_b=[v/sum(b) for v in b]
    naive_ratio=norm(diff(naive_a,naive_b),[-1,-1],[eps,F(1)])/norm(diff(a,b),[-1,-1],[eps,F(1)])
    assert naive_ratio>100
    # Exact primal/dual identities for a two-state alternating chain on one edge.
    dual_cases=[]
    for t in [1,2,3,10,100]:
        d=F(1,1+4*t); D=2*t*d
        q0=D; q1=1-D
        primal=(q0*q0+(q1-1)**2)/2+t*(q1-q0)**2
        u0=D; u1=-D; b01=-d
        assert u0+2*t*b01==0 and u1-2*t*b01==0
        penalty=D*D+t*d*d
        dual=-u1-penalty
        assert primal==dual==F(t,1+4*t)
        assert u0+t*b01!=0 # catches the missing factor2.
        dual_cases.append({'t':t,'primal':str(primal),'dual':str(dual)})
    # Branching anchor lower-bound optimizers; no global retraction inference.
    for k in range(2,101):
        r=F(k*k,k+1); s=F(k,k+1); bound=F(2*k,k+1)
        assert r==k*s
        assert abs(r-(k-1))+(k-1)*abs(s-1)+s==bound
        assert abs(r-k)+k*abs(s-1)==bound
        assert bound>1
    # Discounted hitting relation, endpoint separation, and constant errors.
    for a in [F(1,10),F(1,4),F(2,5),F(49,100)]:
        q=3*a/(1+2*a*a)
        assert a==q*(F(1,3)+F(2,3)*a*a)
        alpha=a/(1+a)
        assert alpha<=F(1,3) and 1-2*alpha>=F(1,3)
    assert F(1,6)**2/F(4)==F(1,144)
    assert F(1,4)**2/F(4)==F(1,64)
    result={'status':'PASS_FINITE_DIAGNOSTICS_NOT_PROOF','normalization_pairs':cases,'mixed_parameter_cases':mixed,'fixed_subprobability_checks':fixed,'max_sampled_ratio':str(maximum),'mixed_boundary_ratio':str(near_ratio),'naive_normalization_negative_control_ratio':str(naive_ratio),'two_state_primal_dual':dual_cases,'branching_anchor_checks':99,'negative_controls':['naive proportional normalization exceeds100','claimed 1-Lipschitz normalization fails at10/7','wrong dual factor fails stationarity','1-contractive branching bound fails'],'limitations':'No finite computation proves full T332, graph asymptotics, universal normalization, or a cotype upper bound.'}
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':main()
