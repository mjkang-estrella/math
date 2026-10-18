#!/usr/bin/env python3
"""Exact finite checks for method obstructions; no evidence of the target bounds.
Copyright Myeongjin Kang. SPDX-License-Identifier: MIT
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

def run():
    rows=[]
    for p in (3,5,7,11,13,17,19,23,29,31):
        s=[(t,t*t%p) for t in range(p)]
        differences=Counter(((u[0]-v[0])%p,(u[1]-v[1])%p) for u in s for v in s)
        sums=Counter(((u[0]+v[0])%p,(u[1]+v[1])%p) for u in s for v in s)
        raw=p*p*sum(v*v for v in differences.values())
        graph=Fraction(p**4*raw,p**8)
        assert raw==2*p**4-p**3
        assert graph==2-Fraction(1,p)
        assert max(sums.values())<=2
        eta=Fraction(1,p**4)
        bound=(p*p*(1-eta)**2/2-1)/(p*p-1)
        assert bound>0
        rows.append({'p':p,'raw_K22':raw,'normalized_K22':str(graph),
                     'max_middle_candidates':max(sums.values()),
                     'conditional_norm_squared_lower_bound':str(bound)})
    rational=[]
    for a,b in ((2,3),(3,4),(3,5),(4,5),(4,7),(5,7)):
        for n in range(1,11):
            vals=[sum(bit*a**i*b**(n-1-i) for i,bit in enumerate(bits))
                  for bits in product((0,1),repeat=n)]
            assert len(set(vals))==2**n
            if n>1:
                sv=sorted(vals)
                assert min(y-x for x,y in zip(sv,sv[1:]))>=1
            rational.append({'a':a,'b':b,'n':n,'distinct_prefixes':len(set(vals))})
    return {'status':'PASS','claims_tested':'finite checks of exact barrier identities only',
            'parabola_cases':rows,'rational_prefix_cases':rational,
            'target182_proved':False,'target153_proved':False,'count_increment':0}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
