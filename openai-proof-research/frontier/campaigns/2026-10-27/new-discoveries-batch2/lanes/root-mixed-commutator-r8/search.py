#!/usr/bin/env python3
"""Bounded numerical research only; assertions do not prove the conjecture."""
from pathlib import Path
import json
import numpy as np

rng=np.random.default_rng(220810005)

def objective(x,y,q):
    ab=x@y; ba=y@x
    return float(np.vdot(ab-ba,ab-q*ba).real)

def operator_fixed_x(x,q):
    n=len(x); eye=np.eye(n)
    left=np.kron(eye,x); right=np.kron(x.T,eye)
    c=left-right; cq=left-q*right
    return (c.conj().T@cq+cq.conj().T@c)/2

def operator_fixed_y(y,q):
    n=len(y); eye=np.eye(n)
    first=np.kron(y.T,eye); second=np.kron(eye,y)
    c=first-second; cq=first-q*second
    return (c.conj().T@cq+cq.conj().T@c)/2

def random_unit(n):
    a=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
    return a/np.linalg.norm(a)

def top_matrix(op,n):
    e,v=np.linalg.eigh(op)
    return v[:,-1].reshape((n,n),order='F'),float(e[-1])

# Test each separate operator against the literal target, including q<0.
for n in (2,3,4):
    for q in (-100.,-2.,-1.,0.,.1,.5,1.,2.,100.):
        x=random_unit(n);y=random_unit(n)
        vx=x.reshape(-1,order='F');vy=y.reshape(-1,order='F')
        f=objective(x,y,q)
        assert abs(np.vdot(vy,operator_fixed_x(x,q)@vy).real-f)<1e-10
        assert abs(np.vdot(vx,operator_fixed_y(y,q)@vx).real-f)<1e-10

results=[]
best_excess=-float('inf')
for n in (2,3,4,5,6):
    for q in (-100.,-5.,-2.,-1.,-.5,0.,.05,.25,.5,1.,2.,5.,100.):
        sharp=(1+q+np.sqrt(2*(1+q*q)))/2
        best=-float('inf')
        for start in range(12):
            x=random_unit(n)
            previous=-float('inf')
            for iteration in range(65):
                y,_=top_matrix(operator_fixed_x(x,q),n)
                x,_=top_matrix(operator_fixed_y(y,q),n)
                f=objective(x,y,q)
                assert f>=previous-1e-8
                if abs(f-previous)<1e-11*max(1.,sharp):break
                previous=f
            if f>best:
                best=f;bx=x.copy();by=y.copy()
        excess=best-sharp
        row={'n':n,'q':q,'sharp_conjectured':float(sharp),'found':float(best),
             'excess':float(excess),'starts':12,'maximum_iterations':65}
        results.append(row)
        if excess>best_excess:
            best_excess=excess
        if excess>1e-7*max(1.,sharp):
            np.savez(Path(__file__).with_name('possible-witness.npz'),x=bx,y=by,q=q)
            print('POSSIBLE VIOLATION: exactification required',row,flush=True)
        print(n,q,f'{best/sharp:.12f}',flush=True)

out={'status':'FINITE NUMERICAL EVIDENCE ONLY','seed':220810005,
     'operator_identity_checks':54,'cells':len(results),'best_excess':float(best_excess),
     'results':results,'new_proof':False,'credit':0}
Path(__file__).with_name('search-results.json').write_text(json.dumps(out,indent=2)+'\n')
