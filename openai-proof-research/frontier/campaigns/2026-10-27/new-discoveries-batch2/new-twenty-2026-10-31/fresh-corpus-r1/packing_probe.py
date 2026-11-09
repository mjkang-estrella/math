import itertools,json,time
import numpy as np
from scipy.optimize import minimize
from pathlib import Path
p=Path(__file__).resolve().parent
rng=np.random.default_rng(340297);out=[]
for m in [2,3,4,5]:
 for perm in itertools.permutations(range(1,m+1)):
  if any(perm[perm[i]-1]!=i+1 for i in range(m)):continue
  n=m+1;pts=[(0,0)]+list(enumerate(perm,1));opts=[]
  for i,j in pts:
   opts.append([(i,j,r,t) for r in range(i+1,n+1) for t in range(j+1,n+1) if not any(i<a<r and j<b<t for a,b in pts)]+[(i,j,i,j)])
  pack=[]
  def go(k,rs):
   if k==n:
    pack.append(rs);return
   for r in opts[k]:
    if all(r[2]<=s[0] or s[2]<=r[0] or r[3]<=s[1] or s[3]<=r[1] or r[0]==r[2] or s[0]==s[2] for s in rs):go(k+1,rs+[r])
  go(0,[])
  # remove dominated packings (any zero rectangle cannot be optimal for strictly interior anchors)
  pack=[r for r in pack if all(a<c for a,b,c,d in r)]
  a=np.zeros((len(pack),n+1,n+1))
  for z,rs in enumerate(pack):
   for i,j,r,t in rs:a[z,r,t]+=1;a[z,i,t]-=1;a[z,r,j]-=1;a[z,i,j]+=1
  a=np.unique(a,axis=0)
  def val(v):
   x=np.r_[0,v[:m],1];y=np.r_[0,v[m:2*m],1];return np.einsum('i,kij,j->k',x,a,y)
  def jac(v):
   x=np.r_[0,v[:m],1];y=np.r_[0,v[m:2*m],1]
   return np.c_[-np.einsum('kij,j->ki',a,y)[:,1:n],-np.einsum('i,kij->kj',x,a)[:,1:n],np.ones(len(a))]
  cons=[{'type':'ineq','fun':lambda v:v[-1]-val(v),'jac':jac}, {'type':'ineq','fun':lambda v: np.r_[np.diff(v[:m]),np.diff(v[m:2*m])]}]
  runs=[]
  for z in range(3):
   xx=np.arange(1,n)/n if z==0 else np.sort(rng.uniform(.05,.95,m));yy=np.arange(1,n)/n if z==0 else np.sort(rng.uniform(.05,.95,m));v=np.r_[xx,yy,1.]
   r=minimize(lambda v:v[-1],v,jac=lambda v:np.r_[np.zeros(2*m),1],constraints=cons,bounds=[(.0001,.9999)]*(2*m)+[(0,1)],method='SLSQP', options={'maxiter':250,'ftol':1e-11})
   runs.append(dict(success=bool(r.success),area=float(max(val(r.x))),x=r.x[:m].tolist(),y=r.x[m:2*m].tolist(),symmetry_gap=float(max(abs(r.x[i-1]-r.x[m+i-1]) for i in range(1,n))),message=r.message))
  item=dict(perm=perm,packing_forms=len(a),runs=runs);out.append(item);print(json.dumps(item),flush=True)
(p/'packing-probe.json').write_text(json.dumps(out,indent=2))
