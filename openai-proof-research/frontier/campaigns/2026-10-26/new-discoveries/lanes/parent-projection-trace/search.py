"""Exploration of literal Banica--Nechita 1602.04456 Conjecture 6.6.

No mathematical certificate or discovery credit is inferred from floating point.
"""
import json
import time
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(261026)


def polar_pair(u, w):
    x = np.concatenate([u, w], axis=1)
    d, v = np.linalg.eigh(x.T @ x)
    if d.min() < 1e-10:
        return None
    y = x @ ((v / np.sqrt(d)) @ v.T)
    return y[:, :u.shape[1]], y[:, u.shape[1]:]


def deficit(x, k, a, b, witness=False):
    r = a+b
    basis = np.eye(k)[:, :r]
    u, v = basis[:, :a], basis[:, a:]
    w_z, rr = np.linalg.qr(x.reshape(k, r), mode='reduced')
    if np.min(np.abs(np.diag(rr))) < 1e-10:
        return 1e3
    w, z = w_z[:, :b], w_z[:, b:]
    p = polar_pair(u, w)
    q = polar_pair(v, z)
    if p is None or q is None:
        return 1e3
    up, wp = p
    vp, zp = q
    left = np.sum((u.T @ w)**2)+np.sum((v.T @ z)**2)
    right = np.sum((up.T @ vp)**2)+np.sum((wp.T @ zp)**2)
    if witness:
        return {'left':float(left), 'right':float(right),
                'w':w.tolist(),'z':z.tolist()}
    return left-right


started = time.monotonic()
results=[]
hit=None
for k,a,b in [(3,1,1),(4,1,1),(5,1,1),(5,1,2),(6,2,2),(7,2,2),(8,2,3)]:
    samples = [(float(deficit(x,k,a,b)), x) for x in rng.normal(size=(5000,k*(a+b)))]
    samples.sort(key=lambda q:q[0])
    best=samples[0]
    for _,x in samples[:12]:
        r=minimize(deficit,x,args=(k,a,b),method='BFGS',options={'maxiter':500,'gtol':1e-9})
        if r.fun<best[0]:best=(float(r.fun),r.x)
    row={'k':k,'a':a,'b':b,'best_deficit':best[0]}
    results.append(row)
    print(row,flush=True)
    if best[0]<-1e-6:
        hit={**row,**deficit(best[1],k,a,b,True)}
        break
Path('search-result.json').write_text(json.dumps({'results':results,'hit':hit,
    'seconds':time.monotonic()-started,'credit':0,'status':'numerical exploration only'},indent=2)+'\n')
