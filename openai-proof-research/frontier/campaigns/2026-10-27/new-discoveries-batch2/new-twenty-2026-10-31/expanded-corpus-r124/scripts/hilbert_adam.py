import sys,pathlib,json
sys.dont_write_bytecode=True
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import numpy as np
rng=np.random.default_rng(124);out=[]
for dim in [4,8,16,32]:
 w=1/np.arange(1,dim+1,dtype=float)**2;ii=np.array([1,2,2,3,3,3]);jj=np.array([0,0,1,0,1,2]);x=rng.random((128,4,dim));best=0;bx=None
 for temp in [.1,.03,.01,.003,.001,.0003]:
  m=np.zeros_like(x);v=m.copy()
  for step in range(1,1001):
   diff=x[:,ii,:]-x[:,jj,:];d=np.sum(diff*diff*w,axis=2);val=d.min(axis=1);ib=val.argmax()
   if val[ib]>best:best=float(val[ib]);bx=x[ib].tolist()
   soft=np.exp(-(d-val[:,None])/temp);soft/=soft.sum(axis=1)[:,None];g=np.zeros_like(x)
   for r,(i,j) in enumerate(zip(ii,jj)):
    z=2*soft[:,r,None]*diff[:,r,:]*w;g[:,i,:]+=z;g[:,j,:]-=z
   m=.9*m+.1*g;v=.999*v+.001*g*g;x=np.clip(x+(.015 if temp>.003 else .002)*m/(1-.9**step)/(np.sqrt(v/(1-.999**step))+1e-8),0,1)
 alpha=np.sqrt(2)*np.pi/3;o=dict(dim=dim,starts=128,steps_per_start=6000,best_squared_distance=best,conjectured_infinite_squared_distance=float(alpha**2-alpha),scaled_points=bx);out.append(o);print(o,flush=True)
(D/'outputs/hilbert-adam.json').write_text(json.dumps(out,indent=2))
