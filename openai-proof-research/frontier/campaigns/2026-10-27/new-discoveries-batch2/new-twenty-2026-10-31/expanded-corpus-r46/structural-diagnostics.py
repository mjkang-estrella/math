import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,pathlib,json,itertools,time
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
import numpy as np
p=pathlib.Path(__file__).resolve().parent;start=time.time()
# Exact finite-grid square closure diagnostic.
out=[]
for w,h in [(3,3),(4,3)]:
 pts=[(x,y) for x in range(w) for y in range(h)];idx={z:i for i,z in enumerate(pts)};squares=set()
 for (x,y),(a,b) in itertools.permutations(pts,2):
  dx,dy=a-x,b-y;z=(a-dy,b+dx);q=(x-dy,y+dx)
  if z in idx and q in idx:squares.add(sum(1<<idx[k] for k in [(x,y),(a,b),z,q]))
 best={};non={}
 for mask in range(1<<len(pts)):
  n=mask.bit_count()
  if n<6:continue
  ss=[s for s in squares if s&mask==s];count=len(ss);closed=False
  for seed in ss:
   c=seed
   while True:
    d=c
    for s in ss:
     if (s&c).bit_count()>=2:c|=s
    if d==c:break
   if c==mask:closed=True;break
  best[n]=max(best.get(n,-1),count)
  if not closed and count>non.get(n,{'squares':-1})['squares']:non[n]={'squares':count,'points':[z for i,z in enumerate(pts) if mask>>i&1]}
 out.append({'grid':[w,h],'grid_maximum':best,'nonrecursive_maximum':non})
(p/'square-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print('square',json.dumps(out),flush=True)
# Standard (n-1,1) block of Schur convolution is B on 1-perp.
from functools import lru_cache
@lru_cache(None)
def perms(n):return np.array(list(itertools.permutations(range(n))),dtype=int)
def per(A):return np.prod(A[np.arange(len(A))[None,:],perms(len(A))],axis=1).sum()
rng=np.random.default_rng(460517);res=[]
for n in [5,6,7]:
 for rank in [2,3]:
  for trial in range(8):
   X=rng.integers(-3,4,(rank,n))+1j*rng.integers(-3,4,(rank,n));A=X.conj().T@X;pa=per(A).real
   B=np.array([[A[i,j]*per(np.delete(np.delete(A,i,axis=0),j,axis=1)) for j in range(n)] for i in range(n)])
   # Compress to perpendicular complement to avoid trivial eigenvalue roundoff.
   Q=np.linalg.qr(np.column_stack([np.ones(n),np.eye(n)[:,:n-1]]))[0][:,1:];eig=float(np.linalg.eigvalsh(Q.conj().T@B@Q)[-1]);res.append({'n':n,'rank':rank,'trial':trial,'ratio':eig/pa,'positive_gap':bool(eig>pa*(1+1e-9))})
(p/'drury-diagnostic.json').write_text(json.dumps({'warning':'floating diagnostic only; no certified eigenvalue comparison','seed':460517,'runs':res,'elapsed_seconds':time.time()-start},indent=2)+'\n');print('drury',json.dumps(res),flush=True)
