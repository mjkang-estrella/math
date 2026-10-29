"""Finite diagnostic only; never a certificate of a supremum or a conjecture."""
import json, math, os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np
from scipy.optimize import minimize_scalar
from pathlib import Path

rng=np.random.default_rng(359807)
angles=np.arange(4096)*2*np.pi/4096
z=np.exp(1j*angles)

def maximum(fun,values):
    # Refine every sampled local maximum, including the periodic seam.
    indices=np.flatnonzero((values>=np.roll(values,1)) & (values>=np.roll(values,-1)))
    best=(-np.inf,0.)
    for i in indices:
        result=minimize_scalar(lambda t:-float(fun(t)),bounds=(angles[i]-2*np.pi/4096,angles[i]+2*np.pi/4096),method='bounded',options={'xatol':1e-12})
        if -result.fun>best[0]:best=(-result.fun,result.x)
    return best

rows=[]
for case in range(300):
    n=2+case%6
    roots=(1+10**rng.uniform(-5,1,n))*np.exp(1j*rng.uniform(0,2*np.pi,n))
    s=rng.integers(2,17,n)/2 # rational weights >= 1
    def vals(theta,deriv=False):
        diff=np.exp(1j*np.asarray(theta))[...,None]-roots
        logf=np.sum(s*np.log(np.abs(diff)),axis=-1)
        return logf+np.log(np.abs(np.sum(s/diff,axis=-1))) if deriv else logf
    mf,tf=maximum(vals,vals(angles))
    md,td=maximum(lambda t:vals(t,True),vals(angles,True))
    ratio=math.exp(md-mf)*2/s.sum()
    q=abs(np.sum(s*np.exp(1j*td)/(np.exp(1j*td)-roots)))*2/s.sum()
    rows.append({'case':case,'n':n,'ratio':ratio,'normalized_logderivative_at_derivative_max':q,'roots':[[a.real,a.imag] for a in roots],'weights':s.tolist()})
out={'seed':359807,'cases':len(rows),'evidence_only':True,'max_ratio':max(x['ratio'] for x in rows),'violations':[x for x in rows if x['ratio']>1+1e-8],'local_method_obstructions':[x for x in rows if x['normalized_logderivative_at_derivative_max']>1+1e-8],'best':sorted(rows,key=lambda x:-x['ratio'])[:5]}
Path(__file__).with_name('probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:(len(v) if isinstance(v,list) else v) for k,v in out.items()}))
