#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT. Exact semantic controls, not a geometry proof."""
from fractions import Fraction as Q
import json
from checked_run import failed

def favored(a,b,e): return a-b*b+Q(2,5)*e-2*e*e
def other(a,b,e): return b-a*a-Q(13,4)*e-2*e*e

def main():
    counts={'first':0,'large':0,'small':0,'inside_actual_chart':0}
    for e in [Q(1,50),Q(1,100),Q(1,1000),Q(1,10000)]:
        for b in sorted(set([Q(0),Q(1,1000),Q(1,100),Q(1,25),Q(1,20),Q(1,10),2*e,4*e,5*e])):
            if b>Q(1,10): continue
            for a in sorted(set([Q(0),b*b/2,b*b,2*b*b])):
                f,o=favored(a,b,e),other(a,b,e)
                if b*b<=a:
                    counts['first']+=1; assert f>=Q(9,25)*e
                elif b>=4*e:
                    counts['large']+=1; assert a*a<b/Q(1000); assert o>Q(353,500)*e
                else:
                    counts['small']+=1; assert f>e/25
                assert max(f,o)>e/25
                if a*a+b*b<Q(1,432): counts['inside_actual_chart']+=1
    assert min(counts.values())>0
    # These exact witnesses demonstrate genuine failure of tempting contract changes.
    assert max(favored(0,0,0),other(0,0,0))==0
    assert max(favored(0,0,Q(1,4)),other(0,0,Q(1,4)))<0
    assert max(favored(-1,0,Q(1,50)),other(-1,0,Q(1,50)))<0
    assert max(favored(2,2,Q(1,50)),other(2,2,Q(1,50)))<0
    assert favored(0,0,Q(1,50))<Q(19,50)*Q(1,50)
    assert other(0,Q(1,25),Q(1,100))<Q(4,5)*Q(1,100)
    # A zero exit code must never mask a printed failure.
    assert failed(0,'SOME FAIL','') and failed(0,'','error: proof failed')
    assert failed(1,'','') and not failed(0,'PASS','')
    print(json.dumps({'status':'PASS exact rational semantic controls','counts':counts,
                      'universal_result_certified_by':'Lean, not this bounded enumeration',
                      'full_B8C_formalized':False},sort_keys=True))

if __name__=='__main__': main()
