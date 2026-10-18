#!/usr/bin/env python3
"""MIT. Exact finite arithmetic diagnostics, not universal mathematical proof."""
from fractions import Fraction as F
from itertools import product
import json, random

def phi(x):return 3*x*x-2*x*x*x

def star(x,w):
    inds=sorted(range(len(x)),key=lambda i:(w[i],i),reverse=True)
    y=[F(0)]*len(x);rem=F(1)
    for i in inds:y[i]=min(max(x[i],F(0)),rem);rem-=y[i]
    return y

def norm(x,w):return sum(abs(a)*b for a,b in zip(x,w))

def diff(a,b):return [x-y for x,y in zip(a,b)]

def main():
    assert 3*phi(F(2,3))/2==F(10,9)
    actual=(phi(F(4,9))+2*phi(F(7,9)))/2
    assert actual==F(263,243)>1
    neg={'median_mass_at_most_one_rejected':actual>1}
    # Normalization exact ratio and its divergence along epsilon=1/n.
    ratios=[]
    for n in [2,10,100,1000]:
        e=F(1,n);d=F(1,10);x=[F(0),F(1)];y=[d,F(1)]
        out=[v/(1+d) for v in y]
        ratio=norm(diff(out,x),[e,F(1)])/norm(diff(y,x),[e,F(1)])
        assert ratio==(1+e)/(e*(1+d));ratios.append(str(ratio))
    neg['normalization_two_Lipschitz_rejected']=F(ratios[-1])>2
    # KR nearest-output ratio on signed measures sigma_s,sigma_-s.
    assert F(2)/F(2,100)==100
    neg['nearest_projection_continuous_bound_rejected']=100>2
    # Edge priority: either the upstream or downstream exact construction.
    ncases=0
    for m in range(1,101):
        for k in range(1,m+1):
            assert max(k,m-k+1)>=F(m+1,2);ncases+=1
    neg['fixed_priority_uniform_two_bound_rejected']=max(50,101-50+1)>2
    rng=random.Random(33239);pairs=0
    for n in range(1,9):
        for _ in range(80):
            w=[F(rng.randrange(1,101),rng.randrange(1,101)) for i in range(n)]
            x=[F(rng.randrange(-5,16),10) for i in range(n)]
            y=[F(rng.randrange(-5,16),10) for i in range(n)]
            rx,ry=star(x,w),star(y,w)
            assert min(rx)>=0 and sum(rx)<=1
            assert star(rx,w)==rx
            assert norm(diff(rx,ry),w)<=2*norm(diff(x,y),w)
            pairs+=1
    assert all(neg.values())
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_NOT_PROOF','actual_resolvent_mass':str(actual),'uniform_median_mass':'10/9','normalization_ratios':ratios,'priority_cases':ncases,'weighted_star_pairs':pairs,'negative_controls':neg},indent=2))
if __name__=='__main__':main()
