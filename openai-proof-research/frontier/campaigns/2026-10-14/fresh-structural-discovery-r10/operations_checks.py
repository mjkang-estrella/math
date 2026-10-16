#!/usr/bin/env python3
"""Exact transfer obstructions and independent normalized-bar diagnostics.

Original code MIT, Myeongjin Kang. No writes, network, or local imports
except the hash-authenticated arithmetic library.
"""
from pathlib import Path
import hashlib
import runpy
import json
from itertools import product
from fractions import Fraction as F

p=Path(__file__).resolve().with_name('tate_checks.py')
assert hashlib.sha256(p.read_bytes()).hexdigest()=='fdf2bc99a32416f72babbe5ab87b07015e41ff97444af5ea2c3a0d50ee728b07'
ns=runpy.run_path(str(p),run_name='authenticated_library')
Q,betti,table,pure,rref=[ns[k] for k in ['Quotient','betti','table','pure','rref']]


def bar(q,r,maxp):
    # Normalized two-sided bar M tensor R_+^{tensor p} tensor k.
    # It computes Tor over any augmented algebra. It does not use f gradients,
    # exterior signs, divided-power labels, or a complete-intersection formula.
    rp=tuple(m for d in range(1,r.top+1) for m in r.basis[d])
    mb=tuple(m for d in range(q.top+1) for m in q.basis[d])
    bases={p:tuple((m,)+word for m in mb for word in product(rp,repeat=p))
           for p in range(maxp+2)}
    maxj=q.top+maxp*r.top
    answer={}
    for j in range(maxj+1):
        dims=[];ranks=[];mats=[]
        for p in range(maxp+2):
            dom=tuple(x for x in bases[p] if sum(map(sum,x))==j)
            tar=tuple(x for x in bases.get(p-1,()) if sum(map(sum,x))==j)
            pos={x:i for i,x in enumerate(tar)}
            cols=[]
            for x in dom:
                col={}
                for a in range(p):
                    ring=q if a==0 else r
                    mul=ring.mul(x[a],{x[a+1]:F(1)})
                    for y,c in mul.items():
                        key=x[:a]+(y,)+x[a+2:]
                        h=pos[key]
                        col[h]=col.get(h,F(0))+(-1)**a*c
                        if not col[h]:del col[h]
                cols.append(col)
            if p>=2:assert ns['compose_zero'](mats[p-1],cols)
            mats.append(cols);dims.append(len(dom));ranks.append(len(rref(cols,len(tar))))
        for p in range(maxp+1):
            b=dims[p]-ranks[p]-ranks[p+1]
            assert b>=0
            if b:answer[(p,j)]=b
    return answer


def quaternion(a,b):
    # Basis 1,i,j,k, Hamilton division algebra over Q.
    out=[F(0)]*4
    tab=[[(0,1),(1,1),(2,1),(3,1)],
         [(1,1),(0,-1),(3,1),(2,-1)],
         [(2,1),(3,-1),(0,-1),(1,1)],
         [(3,1),(2,1),(1,-1),(0,-1)]]
    for x,c in enumerate(a):
        for y,d in enumerate(b):
            z,s=tab[x][y];out[z]+=c*d*s
    return tuple(out)


def main():
    # This example satisfies the full commuting/basis/triangular hypotheses
    # over C with Delta=C, yet the direct right T-action does not factor by P.
    fs=[{(2,0):1,(1,1):-1},{(0,2):1}]
    r=Q(2,fs,2)
    xx=r.reduce({(2,0):1},2)
    xy=r.reduce({(1,1):1},2)
    assert xx==xy and xy
    assert r.hf()==(1,2,1)
    # Independent low-degree normalized-bar/Tate comparisons.
    cases=[]
    for name,n,fs,extra in [
        ('binary-mixed',2,[{(1,1):1},{(3,0):1,(0,3):1}],[{(1,0):1}]),
        ('ternary-nonsplit',3,[{(2,0,0):1,(0,1,1):1},
                             {(0,2,0):1,(1,0,1):1},
                             {(0,0,2):1,(1,1,0):1}],[{(1,0,0):1}])]:
        top=sum(sum(next(iter(f)))-1 for f in fs)
        ring=Q(n,fs,top);m=Q(n,fs+extra,top)
        t,_=betti(m,fs,2);b=bar(m,ring,2)
        assert t==b
        cases.append({'name':name,'p_range':[0,2],'table':table(t,2)})
    one=(1,0,0,0);ii=(0,1,0,0);jj=(0,0,1,0);kk=(0,0,0,1)
    assert quaternion(ii,ii)==(-1,0,0,0)
    assert quaternion(jj,jj)==(-1,0,0,0)
    assert quaternion(ii,jj)==kk
    assert quaternion(jj,ii)==tuple(-x for x in kk)
    # t2*i=(-1)*x + (-k)*y, whereas -i*t2-2*t1 has the same coefficients.
    lhsx=quaternion(ii,ii);lhsy=quaternion(jj,ii)
    rhsx=tuple(-x-2*y for x,y in zip(quaternion(ii,ii),one))
    rhsy=tuple(-x for x in quaternion(ii,jj))
    assert (lhsx,lhsy)==(rhsx,rhsy)
    assert rhsx!=tuple(-x for x in quaternion(ii,ii)), 'missing -2t1 control'
    print(json.dumps({'status':'PASS_SUPPORT_ONLY_C_UNRESOLVED',
                      'direct_quotient_action_obstruction':{'hf':r.hf(),'x_squared_equals_nonzero_xy':True},
                      'quaternion_filtration_obstruction':True,
                      'independent_bar_comparisons':cases,
                      'limits':'bar comparisons through p=2 only; obstructions reject shortcuts, not C'},
                     indent=2,sort_keys=True))


if __name__=='__main__':main()
