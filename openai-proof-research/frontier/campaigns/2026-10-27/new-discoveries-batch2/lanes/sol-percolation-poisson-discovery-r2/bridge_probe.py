"""Five-edge Wheatstone Poisson capacities; exact state support, FLOAT weights.
Run with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python bridge_probe.py.
Hard virtual-address-space cap 512 MiB, including imports; no stochastic sampling.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import numpy as np
from scipy.special import gammainc,gammaincc,gammaincinv
import json,itertools,time
from pathlib import Path
K=10
# s-u=A, s-v=B, u-t=C, v-t=D, u-v=E.
a,b,c,d,e=np.ogrid[tuple(slice(K+1) for _ in range(5))]
f=np.minimum(np.minimum(a+b,c+d),np.minimum(a+d+e,b+c+e)).clip(0,K).astype(np.uint8)
def law(r):
 w=[]
 for lam in r:
  p=np.empty(K+1);p[0]=np.exp(-lam)
  for j in range(1,K):p[j]=p[j-1]*lam/j
  p[K]=gammainc(K,lam);w.append(p)
 weights=w[0][:,None,None,None,None]*w[1][None,:,None,None,None]*w[2][None,None,:,None,None]*w[3][None,None,None,:,None]*w[4][None,None,None,None,:]
 q=np.bincount(f.ravel(),weights.ravel(),minlength=K+1)
 assert abs(q.sum()-1)<1e-12
 tails=np.cumsum(q[::-1])[::-1][1:]
 return q,tails,gammaincinv(np.arange(1,K+1),tails)
def main():
 rng=np.random.default_rng(20261029);best=None;triggers=[];n=0;ulc_bad=[];start=time.time()
 # Deliberate imbalance / bridge regimes, plus bounded log-scale points.
 rates=[.05,.2,1.,4.,12.]
 vectors=list(itertools.product(rates,repeat=5))
 vectors.extend(np.exp(rng.uniform(np.log(.03),np.log(20),size=(1000,5))).tolist())
 for i,r in enumerate(vectors):
  q,t,l=law(r)
  for j in range(K-1):
   if not (1e-11<t[j]<1-1e-11 and 1e-11<t[j+1]<1-1e-11):continue
   n+=1;gap=float(l[j]-l[j+1]);rec=dict(trial=i,rates=r,k=j+1,gap=gap,tails=t.tolist(),lambdas=l.tolist())
   if best is None or gap<best['gap']:best=rec
   if gap< -1e-8:triggers.append(rec)
  for j in range(1,K-1):
   # necessary inequality for ultra-log-concavity of pmf
   if min(q[j-1:j+2])>1e-11 and j*q[j]**2 < (j+1)*q[j-1]*q[j+1]-1e-12:
    if len(ulc_bad)<4:ulc_bad.append(dict(trial=i,rates=r,k=j,pmf=q.tolist()))
 out=dict(model='Wheatstone independent Poisson capacities clipped at 10',states=int(f.size),trials=len(vectors),usable_comparisons=n,triggers=triggers,best=best,ulc_failures_examples=ulc_bad,seconds=time.time()-start,maxrss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,hard_RLIMIT_AS_bytes=512*1024**2,status='numerical diagnostics only; no theorem')
 (Path(__file__).resolve().parent/'bridge-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
