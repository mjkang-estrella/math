"""Finite exploratory search after the proved common-power reduction."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import json,math
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar
rng=np.random.default_rng(359808)
grid=np.arange(2048)*2*np.pi/2048

def sup(fn):
    v=fn(grid); peaks=np.flatnonzero((v>=np.roll(v,1))&(v>=np.roll(v,-1)))
    best=(-np.inf,0.)
    for k in peaks:
        r=minimize_scalar(lambda t:-float(fn(t)),bounds=(grid[k]-2*np.pi/2048,grid[k]+2*np.pi/2048),method='bounded',options={'xatol':1e-12})
        if -r.fun>best[0]:best=(-r.fun,float(r.x))
    return best

results=[]
for k in range(1800):
    n=2+k%7
    roots=(1+10**rng.uniform(-6,1,n))*np.exp(1j*rng.uniform(0,2*np.pi,n))
    s=1+np.maximum(1,np.round(10**rng.uniform(0,4,n)))/1000
    s[0]=1
    if k%3==0:roots[1:]*=np.exp(-1j*np.angle(roots[1:])); roots[0]=1+1j*10**rng.uniform(-5,-1);roots[1]=-3-roots[0].imag*1j
    def logf(t,derivative=False):
        d=np.exp(1j*np.asarray(t))[...,None]-roots
        value=np.sum(s*np.log(np.abs(d)),axis=-1)
        return value+np.log(np.abs(np.sum(s/d,axis=-1))) if derivative else value
    mf,tf=sup(logf);md,td=sup(lambda t:logf(t,True))
    ratio=math.exp(md-mf)*2/s.sum()
    local=abs(np.sum(s/(np.exp(1j*td)-roots)))*2/s.sum()
    results.append({'case':k,'n':n,'ratio':ratio,'local_ratio':float(local),'weights':s.tolist(),'roots':[[a.real,a.imag] for a in roots]})
out={'seed':359808,'case_count':len(results),'evidence_only':True,'supremum_certified':False,'max_ratio':max(r['ratio'] for r in results),'violations':[r for r in results if r['ratio']>1+1e-7],'local_obstruction_count':sum(r['local_ratio']>1+1e-7 for r in results),'largest_local_obstruction':max(results,key=lambda r:r['local_ratio']),'best':sorted(results,key=lambda r:-r['ratio'])[:5]}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps({k:(len(v) if isinstance(v,list) else v) for k,v in out.items() if k!='largest_local_obstruction'}))
