import numpy as np,json
from pathlib import Path
rng=np.random.default_rng(20261026)
def power(B,t):
 v,U=np.linalg.eigh(B)
 if np.min(v)<=0:raise ValueError
 return (U*(v**t))@U.T
best=0
for n in [2,3,4]:
 for it in range(30000):
  p=rng.uniform(.15,2);q=p+rng.uniform(.1,3);r=rng.uniform(p,5)
  av=np.exp(rng.uniform(-1.8,1.8,n));bv=np.exp(rng.uniform(-1.8,1.8,n));U=np.linalg.qr(rng.normal(size=(n,n)))[0]
  B=(U*bv)@U.T
  L=(av**((r+q)/2))[:,None]*power(B,q)*(av**((r+q)/2))[None,:]
  T=(av**(p/2))[:,None]*power(B,p)*(av**(p/2))[None,:]
  R=(av**(r/2))[:,None]*power(T,q/p)*(av**(r/2))[None,:]
  evL=np.linalg.eigvalsh(L)[::-1];evR=np.linalg.eigvalsh(R)[::-1]
  if min(evL.min(),evR.min())<=1e-7:continue
  ds=np.cumsum(np.log(evL)-np.log(evR))[:-1]
  m=ds.min()
  if m<best:
   best=m
   if m< -1e-7:
    d={'n':n,'iteration':it,'p':p,'q':q,'r':r,'av':av.tolist(),'B':B.tolist(),'gaplog':ds.tolist()};Path('third-discovery/reverse-blp-hit.json').write_text(json.dumps(d,indent=2));print(d,flush=True);raise SystemExit
 print(n,'nohit',best,flush=True)
