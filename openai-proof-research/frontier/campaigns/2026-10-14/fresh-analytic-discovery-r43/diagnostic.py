#!/usr/bin/env python3
"""MIT. Finite arithmetic checks; not proof of asymptotics or recurrence."""
from fractions import Fraction as F
from collections import defaultdict
from math import factorial
import json


def rates(i,b):
    return [([1],(1,0)),([i,1],(-1,0)),
            ([i*(i-1),2*i-1,1],(1,1)),
            ([b*i*(i-1)*(i-2),b*(3*i*i-6*i+2),b*(3*i-3),b],(-1,-1))]


def transition_series(i,b):
    rs=rates(i,b)
    total=[sum(p[j] if j<len(p) else 0 for p,_ in rs) for j in range(4)]
    degree=max(j for j,c in enumerate(total) if c)
    out=[]
    for p,move in rs:
        lead=p[degree] if degree<len(p) else 0
        sub=p[degree-1] if degree-1<len(p) else 0
        q0=F(lead,total[degree])
        q1=(sub-q0*total[degree-1])/total[degree]
        out.append((move,q0,q1))
    assert sum(r[1] for r in out)==1 and sum(r[2] for r in out)==0
    return out


def formal(maxk):
    dist={(0,0):(F(1),F(0))};rows=[]
    for k in range(1,maxk+1):
        nxt=defaultdict(lambda:[F(0),F(0)])
        for (i,b),(c0,c1) in dist.items():
            for (di,db),q0,q1 in transition_series(i,b):
                if not q0 and not q1:continue
                dst=nxt[i+di,b+db]
                dst[0]+=c0*q0;dst[1]+=c1*q0+c0*q1
        dist={key:tuple(v) for key,v in nxt.items() if v != [0,0]}
        a0=sum(i*v[0] for (i,b),v in dist.items())
        a1=sum(i*v[1] for (i,b),v in dist.items())
        want=(F(1),F(-k-1)) if k%2 else (F(0),F(2))
        assert (a0,a1)==want
        rows.append({'k':k,'constant':str(a0),'inverse_N':str(a1)})
    return rows


def detailed_balance():
    for a in range(12):
        for b in range(12):
            pi=F(1,factorial(a)*factorial(b))
            assert pi == (a+1)*F(1,factorial(a+1)*factorial(b))
            lhs=pi*a*(a-1)
            rhs=F(1,factorial(a+1)*factorial(b+1))*(a+1)*a*(a-1)*(b+1)
            assert lhs==rhs
    # Deliberately wrong geometric stationary weights fail even the linear pair.
    assert F(1,2**(3+2)) != 4*F(1,2**(4+2))


def finite_float(N,maxk):
    dist={(0,0):1.0};out=[]
    for k in range(1,maxk+1):
        nxt=defaultdict(float)
        for (i,b),p in dist.items():
            r=[(sum(c*N**j for j,c in enumerate(poly)),move) for poly,move in rates(i,b)]
            z=sum(x for x,_ in r)
            for q,(di,db) in r:
                if q:nxt[i+di,b+db]+=p*q/z
        dist=nxt
        drift=sum(i*p for (i,b),p in dist.items())
        assert drift>0
        out.append({'k':k,'N':N,'A_drift':drift})
    return out


def main():
    rows=formal(40);detailed_balance()
    # Two deliberately false proposed repairs: no even boundary term, or negative term.
    assert rows[1]['inverse_N']!='0'
    assert rows[1]['inverse_N']!='-2'
    print(json.dumps({'status':'PASS_FINITE_DIAGNOSTIC_NOT_PROOF',
      'formal_series':rows,'finite_float_examples':finite_float(10000,10),
      'negative_controls':['zero_even_coefficient_rejected','negative_even_coefficient_rejected','geometric_balance_rejected']},sort_keys=True,indent=2))

if __name__=='__main__':main()
