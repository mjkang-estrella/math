#!/usr/bin/env python3
"""Bounded test of Laszlo's real alternating-three-matrix conjecture."""
import json
from pathlib import Path
import numpy as np
from scipy.linalg import eigh
rng=np.random.default_rng(20221013001)

def comm(a,b):return a@b-b@a
def mass(a):return float(np.vdot(a,a).real)
def alt(a,b,c):return a@b@c+b@c@a+c@a@b-c@b@a-a@c@b-b@a@c
def denominator(a,b,c):
    return mass(a)*mass(comm(b,c))+mass(b)*mass(comm(c,a))+mass(c)*mass(comm(a,b))
def operators(b,c):
    n=len(b);I=np.eye(n);bc=comm(b,c)
    lb=np.kron(I,b);rb=np.kron(b.T,I)
    lc=np.kron(I,c);rc=np.kron(c.T,I)
    t=np.kron(bc.T,I)+np.kron(I,bc)+lc@rb-lb@rc
    ab=lb-rb;ac=lc-rc
    den=mass(bc)*np.eye(n*n)+mass(b)*(ac.conj().T@ac)+mass(c)*(ab.conj().T@ab)
    return t,t.conj().T@t,den
def random_unit(n,cplx=False):
    a=rng.normal(size=(n,n))
    if cplx:a=a+1j*rng.normal(size=(n,n))
    return a/np.linalg.norm(a)

for cplx in (False,True):
    for n in (2,3,4):
        a,b,c=(random_unit(n,cplx) for _ in range(3))
        t,num,den=operators(b,c);v=a.reshape(-1,order='F')
        assert np.linalg.norm((t@v).reshape((n,n),order='F')-alt(a,b,c))<1e-12
        assert abs(np.vdot(v,den@v).real-denominator(a,b,c))<1e-11

rows=[]
for cplx in (False,True):
    for n in (2,3,4,5,6,8):
        best=0.
        for start in range(20):
            a,b,c=(random_unit(n,cplx) for _ in range(3))
            previous=0.
            for it in range(50):
                for _ in range(3):
                    _,num,den=operators(b,c)
                    es,vs=eigh(num,den,subset_by_index=(n*n-1,n*n-1))
                    a=vs[:,-1].reshape((n,n),order='F');a=a/np.linalg.norm(a)
                    a,b,c=b,c,a
                value=mass(alt(a,b,c))/denominator(a,b,c)
                assert value>=previous-1e-7
                if abs(value-previous)<1e-11:break
                previous=value
            if value>best:best=value;ba=a.copy();bb=b.copy();bc=c.copy()
        row={'field':'complex diagnostic' if cplx else 'real source',
             'n':n,'found_ratio':float(best),'source_constant':1.5,
             'starts':20,'max_iterations':50}
        rows.append(row);print(row,flush=True)
        if best>1.5000001:
            path=Path(__file__).with_name(f'possible-alternating-{n}-{cplx}.npz')
            np.savez(path,a=ba,b=bb,c=bc)
out={'status':'Finite numerical evidence only; no proof or counterexample',
     'operator_identity_checks':12,'seed':20221013001,'rows':rows,'credit':0}
Path(__file__).with_name('alternating-results.json').write_text(json.dumps(out,indent=2)+'\n')
