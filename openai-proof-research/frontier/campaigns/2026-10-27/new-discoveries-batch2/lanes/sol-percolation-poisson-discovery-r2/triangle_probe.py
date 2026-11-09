"""Poisson three-relay triangle, streamed contraction, 512MiB RLIMIT_AS."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import numpy as np
from scipy.special import gammainc,gammaincinv
from pathlib import Path
import itertools,json,time
K=4;edges=[(0,i) for i in [1,2,3]]+[(i,4) for i in [1,2,3]]+[(1,2),(1,3),(2,3)]
shape=(K+1,)*len(edges)
flow=np.full(shape,K,dtype=np.uint8)
# Broadcast only a single cut at once; no configuration-by-edge matrix.
coords=np.ogrid[tuple(slice(K+1) for _ in edges)]
for mask in range(8):
 side={0}|{i+1 for i in range(3) if mask>>i&1}
 cut=sum(coords[j] for j,(u,v) in enumerate(edges) if (u in side)!=(v in side))
 np.minimum(flow,cut,out=flow,casting='unsafe')
del cut,coords
def tails(r):
 ps=[]
 for lam in r:
  p=np.empty(K+1);p[0]=np.exp(-lam)
  for j in range(1,K):p[j]=p[j-1]*lam/j
  p[K]=gammainc(K,lam);ps.append(p)
 ts=[]
 for k in range(1,K+1):
  z=(flow>=k).astype(float)
  for p in ps:z=np.tensordot(p,z,axes=(0,0))
  ts.append(float(z))
 return np.array(ts)
def main():
 start=time.time();rates=[.05,.2,1,4,12]
 vectors=[[a]*3+[b]*3+[c]*3 for a,b,c in itertools.product(rates,repeat=3)]
 rng=np.random.default_rng(30261029)
 for _ in range(400):vectors.append(np.exp(rng.uniform(np.log(.03),np.log(20),9)).tolist())
 best=None;triggers=[];count=0
 for i,r in enumerate(vectors):
  t=tails(r);l=gammaincinv(np.arange(1,K+1),t)
  for j in range(K-1):
   if not(1e-10<t[j]<1-1e-10 and 1e-10<t[j+1]<1-1e-10):continue
   count+=1;gap=float(l[j]-l[j+1]);rec=dict(trial=i,rates=r,k=j+1,gap=gap,tails=t.tolist(),lambdas=l.tolist())
   if best is None or gap<best['gap']:best=rec
   if gap< -1e-8:triggers.append(rec)
 out=dict(status='numerical evidence only',edges=edges,clip=K,states=int(flow.size),trials=len(vectors),usable_comparisons=count,best=best,triggers=triggers,seconds=time.time()-start,maxrss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,hard_RLIMIT_AS_bytes=512*1024**2)
 (Path(__file__).resolve().parent/'triangle-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
