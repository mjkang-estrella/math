#!/usr/bin/env python3
"""Normalized analytic-gradient search; every reported value is finite evidence."""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

rng=np.random.default_rng(20261027)
N=3
d=2


def power_and_grad(X,p):
    u,s,v=np.linalg.svd(X,full_matrices=False)
    return np.sum(s**p), p*(u*s**(p-1))@v


def objective(x,p):
    length=np.linalg.norm(x)
    x=x/length
    parts=x.reshape(2,2,N,d,d)
    blocks=parts[0]+1j*parts[1]
    T=blocks.transpose(0,2,1,3).reshape(2*d,N*d)
    full,gfull=power_and_grad(T,p)
    C=np.empty((2,N))
    block_gradient=np.empty_like(blocks)
    for i in range(2):
        for j in range(N):
            f,g=power_and_grad(blocks[i,j],p)
            C[i,j]=f**(1/p)
            block_gradient[i,j]=(f**(1/p-1)/p)*g
    compressed,gcompressed=power_and_grad(C,p)
    gf=gfull.reshape(2,d,N,d).transpose(0,2,1,3)
    gb=gcompressed[:,:,None,None]*block_gradient/compressed-gf/full
    g=np.stack([gb.real,gb.imag]).ravel()
    g=(g-np.dot(g,x)*x)/length
    value=np.log(compressed/full)
    sign=1 if p<2 else -1
    return -sign*value,-sign*g


test=rng.normal(size=2*2*N*d*d)
value,g=objective(test,1.5)
eps=1e-6
differences=[]
for k in range(0,len(test),5):
    dx=np.zeros_like(test);dx[k]=eps
    finite=(objective(test+dx,1.5)[0]-objective(test-dx,1.5)[0])/(2*eps)
    differences.append(abs(finite-g[k]))
assert max(differences)<1e-7, differences

results=[]
for p in [1.1,1.5,1.9,2.1,2.5,3.0,3.9]:
    best=(float('inf'),None)
    iterations=0
    for trial in range(24):
        start=rng.normal(size=2*2*N*d*d)
        start/=np.linalg.norm(start)
        r=minimize(lambda x:objective(x,p),start,jac=True,method='BFGS',
                   options={'maxiter':600,'gtol':1e-9})
        iterations+=r.nit
        if np.isfinite(r.fun) and r.fun<best[0]:best=(float(r.fun),r.x)
    result={'p':p,'largest_violation_log_ratio':-best[0],
            'largest_violation_ratio':float(np.exp(-best[0])),
            'restarts':24,'iterations':iterations}
    if -best[0]>1e-6:
        file=f'witness-p{p}.npy';np.save(Path(__file__).with_name(file),best[1]);result['candidate_file']=file
    results.append(result)
    print(json.dumps(result),flush=True)
out={'status':'finite numerical evidence only','block_shape':[2,N,d,d],
     'complex_entries':True,'normalization':'joint Frobenius norm one at each evaluation',
     'analytic_gradient_check_max_error':max(differences),'results':results}
Path(__file__).with_name('search-result.json').write_text(json.dumps(out,indent=2)+'\n')
