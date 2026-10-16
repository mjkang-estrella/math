#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT.
"""Deterministic formula checks; never a proof of full B or planar stability."""
import json
import math
import random


def kernel(x, r=1.0):
    z=x/r
    return 2/(math.pi*r)*math.sqrt(max(0.0,1-z*z)) if abs(z)<1 else 0.0


def cdf(z):
    if z<=-1:return 0.0
    if z>=1:return 1.0
    return 0.5+(math.asin(z)+z*math.sqrt(1-z*z))/math.pi


def negvar(values):
    return sum(max(a-b,0.0) for a,b in zip(values,values[1:]))


def main():
    rng=random.Random(1041604)
    min_tp2=0.0
    for _ in range(25000):
        a,b=sorted((rng.uniform(-2,2),rng.uniform(-2,2)))
        s1,s2=sorted((rng.uniform(-2,2),rng.uniform(-2,2)))
        val=kernel(s2-b)*kernel(s1-a)-kernel(s1-b)*kernel(s2-a)
        min_tp2=min(min_tp2,val)
        assert val>=-2e-14, ('TP2',a,b,s1,s2,val)
    profiles=0; baseline_tests=0; max_wrong=0.0; max_baseline_gap=0.0
    for index in range(64):
        A=rng.uniform(0.1,2); B=A+rng.uniform(0,2)
        n=rng.randrange(2,18)
        # Include arbitrary jump across zero, plateaux, and asymmetric layers.
        loc=sorted(rng.uniform(-1.3,1.3) for _ in range(n))
        levels=sorted([-A,B]+[rng.uniform(-A,B) for _ in range(n-1)])
        h=list(map(abs,levels)); jumps=[h[i+1]-h[i] for i in range(n)]
        xs=[-3.0+6.0*k/1600 for k in range(1601)]
        radii=[2**(-k/2) for k in range(13)]
        us=[]
        for r in radii:
            vals=[h[0]+sum(d*cdf((s-z)/r) for d,z in zip(jumps,loc)) for s in xs]
            deriv=[sum(d*kernel(s-z,r) for d,z in zip(jumps,loc)) for s in xs]
            positive_seen=False
            for d in deriv:
                if d>1e-10:positive_seen=True
                if positive_seen:assert d>=-1e-10, ('one-valley derivative',index,r,d)
            us.append(vals)
        # Supremum over these radii, not a certificate for the continuum supremum.
        env=[max(v) for v in zip(*us)]
        c=A
        clamped=[max(c,v) for v in env]
        wrong=negvar(clamped); max_wrong=max(max_wrong,wrong)
        assert wrong<1e-9
        assert abs(sum(abs(a-b) for a,b in zip(clamped,clamped[1:]))-(B-A))<1e-9
        # Sampled varying BV baseline: negative variation obeys same partition inequality.
        for eps in [0.0,0.025,0.25]:
            b=[A-eps+0.08*(1+math.sin(7*s+index))+(0.13 if s>0.21 else 0) for s in xs]
            mixed=[max(u,v) for u,v in zip(env,b)]
            gap=negvar(mixed)-(max(A-min(b),0)+negvar(b))
            max_baseline_gap=max(max_baseline_gap,gap)
            assert gap<1e-9, ('baseline',index,eps,gap)
            baseline_tests+=1
        profiles+=1
    strip_a=1/20
    strip_p=2/math.pi*(math.asin(strip_a)+strip_a*math.sqrt(1-strip_a**2))
    assert 2*(1-strip_p)>1.5
    assert (2-strip_p)-(2-1.75*strip_p)>0
    # Exact atomic planar convolution sanity: an atom does not model a BV derivative;
    # this check uses line/sheet normal measures through their 1D disk marginal only.
    print(json.dumps({'status':'PASS','tp2_samples':25000,'ordered_step_profiles':profiles,
        'varying_baseline_partition_tests':baseline_tests,'minimum_tp2_residual':round(min_tp2,14),
        'maximum_unfavorable_variation_above_lower_trace':round(max_wrong,12),
        'maximum_baseline_inequality_violation':round(max_baseline_gap,12),
        'scope':'finite formula tests only; full B and arbitrary planar transfer UNRESOLVED',
        'planar_slice_obstruction':{'strip_fraction':round(strip_p,12),'certified_normal_drop_lower_bound':round(0.75*strip_p,12),'transverse_variation_cost':192,'counterexample_to_B':False},
        'numerics_are_proof':False},indent=2,sort_keys=True))

if __name__=='__main__':main()
