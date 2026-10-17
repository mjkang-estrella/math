"""Exploratory cyclic Boolean seed MILP; verify returned tables exactly.
Original code: Myeongjin Kang, MIT. Numerical optimality is not a proof.
"""
import json,sys,time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

def rotate(x,n): return ((x<<1)&((1<<n)-1)) | (x>>(n-1))
def orbits(n):
    out=[]; seen=set()
    for x in range(1<<n):
        if x in seen: continue
        o=[]; y=x
        while y not in o: o.append(y); y=rotate(y,n)
        seen.update(o); out.append(o)
    return out

def run(n,d,balance):
    obs=orbits(n); reps=[o[0] for o in obs]
    # Rotation invariance makes one row per dual orbit sufficient.
    masks=[s for s in reps if s.bit_count()>d]
    if balance: masks=[0]+masks
    A=np.array([[sum((-1)**((x&s).bit_count()%2) for x in o) for o in obs] for s in masks],dtype=float)
    c=np.array([len(o)*(n-2*o[0].bit_count()) for o in obs],dtype=float)
    res=milp(-c,integrality=np.ones(len(obs)),bounds=Bounds(0,1),constraints=LinearConstraint(A,A.sum(axis=1)/2,A.sum(axis=1)/2),options={'time_limit':15,'mip_rel_gap':0})
    out={'n':n,'d':d,'balanced_required':balance,'status':int(res.status),'message':res.message,'orbits':len(obs),'constraints':len(masks)}
    if res.x is not None:
        vals=np.rint(res.x).astype(int)*2-1
        table=[0]*(1<<n)
        for o,v in zip(obs,vals):
            for x in o:table[x]=int(v)
        walsh=table[:]; k=1
        while k<len(walsh):
            for i in range(0,len(walsh),2*k):
                for j in range(i,i+k):a,b=walsh[j],walsh[j+k];walsh[j]=a+b;walsh[j+k]=a-b
            k*=2
        degree=max((s.bit_count() for s,v in enumerate(walsh) if v),default=0)
        linear=sum(walsh[1<<i] for i in range(n))
        assert degree<=d and (not balance or walsh[0]==0)
        assert all(table[x]==table[rotate(x,n)] for x in range(1<<n))
        out.update(actual_degree=degree,linear_numerator=linear,denominator=1<<n,mean_numerator=walsh[0],violates_sqrt=linear>0 and linear*linear>degree*(1<<(2*n)),positive_orbit_reps=[int(s) for s,v in zip(reps,vals) if v==1])
        if getattr(res,'mip_dual_bound',None) is not None:out['numerical_upper_L']=float((-2*res.mip_dual_bound-c.sum())/(1<<n))
    return out
if __name__=='__main__':
    n,d,b=map(int,sys.argv[1:]); print(json.dumps(run(n,d,bool(b)),sort_keys=True),flush=True)
