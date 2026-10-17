#!/usr/bin/env python3
"""Finite exact diagnostics only; not a proof of OA057 or any geometry."""
import argparse, json, math
from itertools import product, combinations

def shift(x,a):
    return tuple(x[(k+a)%len(x)] for k in range(len(x)))
def add(x,t,m):
    return tuple((u+t)%m for u in x)
def action(x,a,b,m):
    return add(shift(x,a-b),b,m)
def main():
    counts={'moduli':0,'pair_group_law_cases':0,'equal_power_translation_cases':0,'generator_fixed_vectors':0,'mixed_inertia_cases':0}
    for m in range(2,33):
        counts['moduli']+=1
        x=tuple((k*k+3*k+1)%m for k in range(m))
        for a,b in product(range(m),repeat=2):
            # Check all first elements against three generating/diagonal second elements.
            for c,d in [(1,0),(0,1),(1,1)]:
                assert action(action(x,a,b,m),c,d,m)==action(x,(a+c)%m,(b+d)%m,m)
                counts['pair_group_law_cases']+=1
        for t in range(1,m):
            assert action(x,t,t,m)==add(x,t,m)!=x
            counts['equal_power_translation_cases']+=1
        z=(0,)*m; v=tuple(range(m))
        assert action(z,1,0,m)==z
        assert action(v,0,1,m)==v
        counts['generator_fixed_vectors']+=2
    for n in range(1,6):
        N=n+1
        for orders in [(2,),(3,),(4,),(6,),(2,3),(3,4),(4,6),(2,3,4)]:
            m=math.lcm(*orders)
            for i,mi in enumerate(orders):
                di=m//mi
                # At a point on D_i there are at most n-1 passing auxiliary labels.
                for size in range(min(n-1,N)+1):
                    for present in combinations(range(N),size):
                        absent=[j for j in range(N) if j not in present]
                        assert len(absent)>=2
                        for a in range(1,mi):
                            for aux in [0,1,m-1]:
                                coordinates=[(di*a+(aux if j in present else 0))%m for j in range(N)]
                                t=coordinates[absent[0]]
                                assert t==coordinates[absent[1]] and t!=0
                                assert action((0,)*m,t,t,m)!=(0,)*m
                                counts['mixed_inertia_cases']+=1
    # Negative control: support >=2 is NOT the claimed detector.
    # On Z/6^6, pair coefficients (1,2) have an actual fixed point.
    m=6; x=tuple((2*k)%m for k in range(m))
    assert action(x,1,2,m)==x
    # Negative control: a torsion point of order3 misses diagonal exponent3 at M=6.
    assert add((0,)*6,3*2,6)==(0,)*6
    out={'status':'PASS_FINITE_DIAGNOSTICS','counts':counts,'negative_controls':{'arbitrary_support_claim_refuted':True,'non_exact_torsion_claim_refuted':True},'universal_or_geometric_proof':False}
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=='__main__':main()
