#!/usr/bin/env python3
"""MIT. Small connected planar ribbon maps and exact rational budgets, not proof."""
import json
from fractions import Fraction as F
from math import ceil

def cycles(p):
    left=set(range(len(p)));out=[]
    while left:
        x=min(left);c=[]
        while x in left:c.append(x);left.remove(x);x=p[x]
        out.append(c)
    return out

def matchings(xs):
    if not xs:yield {};return
    a=xs[0]
    for b in xs[1:]:
        for q in matchings([x for x in xs[1:] if x!=b]):
            yield dict(q,**{})|{a:b,b:a}

def ribbon():
    maps=cases=outer_cases=0
    for m in range(1,5):
        n=2*m
        for mask in range(1<<(n-1)):
            starts=[0]+[i+1 for i in range(n-1) if mask>>i&1]+[n]
            vertices=[list(range(a,b)) for a,b in zip(starts,starts[1:])]
            sigma=list(range(n))
            for v in vertices:
                for i,x in enumerate(v):sigma[x]=v[(i+1)%len(v)]
            for ad in matchings(list(range(n))):
                a=[ad[i] for i in range(n)]
                if any(sigma[x]==a[x] for x in range(n)):continue
                seen={0};stack=[0]
                while stack:
                    x=stack.pop()
                    for y in [a[x],sigma[x]]:
                        if y not in seen:seen.add(y);stack.append(y)
                if len(seen)!=n:continue
                if len(vertices)-m+len(cycles([sigma[a[x]] for x in range(n)]))!=2:continue
                maps+=1
                # Gap x is after x and before sigma[x]. Distinct-band digon.
                good={x for x in range(n) if sigma[a[sigma[x]]]==a[x] and a[x]!=sigma[x]}
                opp={x:a[sigma[x]] for x in good}
                assert all(opp[x] in good and opp[opp[x]]==x for x in good)
                nongood=set(range(n))-good
                assert len(nongood)<=8*len(vertices)
                baseline={v[-1] for v in vertices}
                choices=[set(),set(range(n))]+[{x} for x in range(n)]
                for extra in choices:
                    marks=baseline|extra
                    cuts=nongood|marks|{opp[x] for x in marks&good}
                    runs=[]
                    for v in vertices:
                        for x in v:
                            if x not in cuts:continue
                            run=[];y=sigma[x]
                            while True:
                                run.append(y)
                                if y in cuts:break
                                y=sigma[y]
                            runs.append(tuple(run))
                    lookup={r:i for i,r in enumerate(runs)}
                    partners=[]
                    for i,r in enumerate(runs):
                        j=lookup[tuple(a[x] for x in reversed(r))]
                        assert i!=j;partners.append(j)
                    nstar=len(marks)
                    assert len(runs)%2==0 and len(runs)//2<=6*nstar
                    cases+=1
                    # Any designated outer vertex: deleting incident whole runs
                    # loses no more inner occurrences than its degree.
                    for outer in vertices:
                        os=set(outer);lost=0
                        for i,r in enumerate(runs):
                            if not set(r)&os and set(runs[partners[i]])&os:lost+=len(r)
                        assert lost<=len(outer);outer_cases+=1
    return {'connected_planar_maps_up_to_4_edges':maps,'cut_cases':cases,'outer_deletions':outer_cases,
            'limits':'Unique inverse labels per paired edge; connected genus-zero maps only; indexing plus no, one, or all extra cuts. Not exhaustive beyond four edges; no cone-map or separator proof.'}

def budgets():
    count=0
    for eps in [F(1),F(1,2),F(1,17),F(1,100)]:
        for d in [F(1,7),F(1),F(7),F(101,3)]:
            u=max(3,ceil(192*d/eps));eta=min(F(1,32*u),eps/(64*u))
            add=3*d/u;deleted=eta*u;outer=eps/32
            assert add<=eps/64 and deleted<=eps/64 and deleted<=F(1,32)
            deficit=outer+deleted+add
            assert deficit<=eps/16
            kept=F(31,32)-F(1,16)-F(1,16)
            assert kept==F(27,32)>0
            count+=1
    return {'rational_parameter_cases':count,'scope':'Normalized H=1 budgets only; no probabilistic or topological claim.'}

if __name__=='__main__':print(json.dumps({'status':'PASS','ribbon':ribbon(),'budgets':budgets()},indent=2))
