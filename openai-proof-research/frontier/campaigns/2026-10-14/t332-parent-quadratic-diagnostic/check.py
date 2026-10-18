#!/usr/bin/env python3
"""Finite exact checks only. Copyright 2026 Myeongjin Kang. MIT."""
from fractions import Fraction as F
import json

def run():
    rows=[]
    for h in range(1,101):
        delta=F(1,4); t=delta/(2-F(1,2**h))
        q=[F(1,2**(l+1)) for l in range(h+1)]
        r=[t/2**l for l in range(h+1)]
        lam=[1-t*(F(1,2**l)-F(1,2**h)) for l in range(h)]
        assert all(v>0 for v in lam)
        assert 0<q[0]+r[0]<1
        assert all(q[l]+r[l]==2*(q[l+1]+r[l+1]) for l in range(h))
        bt=[lam[0]-1]+[lam[l]-lam[l-1] for l in range(1,h)]+[1-lam[-1]]
        assert bt==[r[0]-delta]+r[1:]
        amplification=sum(2**l*r[l] for l in range(h+1))/delta
        assert amplification==F(h+1)/(2-F(1,2**h))
        assert amplification>F(h+1,2)
        if h in [1,2,4,8,16,32,64,100]:
            rows.append({'depth':h,'ratio':str(amplification)})
    return {'status':'PASS','depths':[1,100],'scope':'finite arithmetic diagnostics, not T332 or a novelty test','samples':rows}

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
