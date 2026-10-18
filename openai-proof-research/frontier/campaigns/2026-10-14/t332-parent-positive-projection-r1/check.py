#!/usr/bin/env python3
"""MIT. Exact finite diagnostic, not proof of the universal obstruction."""
from fractions import Fraction as F
import json

def run():
    cases=[]
    for h in range(1,41):
        eps=F(1,3)
        s=sum((F(1,2**l) for l in range(1,h+1)),F(0))
        r=1/(1+s)
        residual=[eps*(1-r)]+[-eps*r/F(2**l) for l in range(1,h+1)]
        # Pair gradient with every distinct path type, including leaf equality.
        pairings=[sum(residual[:j+1],F(0)) for j in range(h+1)]
        assert all(v>=0 for v in pairings) and pairings[-1]==0
        q=[(1-eps*r)/F(2**l) for l in range(h+1)]
        assert 0<q[0]<=1
        assert all(q[l]==2*q[l+1] for l in range(h))
        outdist=sum((F(2**l)*eps*r/F(2**l) for l in range(h+1)),F(0))
        ratio=outdist/eps
        assert ratio==F(h+1)/(2-F(1,2**h))
        cases.append({'depth':h,'ratio':str(ratio),'ratio_decimal':float(ratio),'dual_pairings_nonnegative':True,'leaf_complementarity':True})
    print(json.dumps({'status':'PASS_FINITE_RATIONAL_DIAGNOSTIC_NOT_PROOF','cases':cases},indent=2))
if __name__=='__main__':run()
