import os
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import numpy as np,json,datetime
from pathlib import Path
rng=np.random.default_rng(373375)
p=Path(__file__).parent
from itertools import combinations
BASE=np.array([[1,0,0,-1,-1],[-1,2,0,0,-1],[-1,-.5,1,0,0],[0,-1,-1,1,0],[0,-.5,-.5,-1,1.]])
A=BASE.copy()
def qualify(A):
 if np.min(np.diag(A))<0:return False
 for i,j in combinations(range(5),2):
  if A[i,j]<0 and A[j,i]<0 and A[i,j]*A[j,i]>A[i,i]*A[j,j]+1e-9:return False
 for ix in combinations(range(5),3):
  B=A[np.ix_(ix,ix)];det=np.linalg.det(B)
  if abs(det)<1e-7:return False
  if np.max(np.linalg.inv(B))<=1e-9:return False
 for ix in combinations(range(5),4):
  B=A[np.ix_(ix,ix)]
  if abs(np.linalg.det(B))<1e-7:return False
  if np.max(np.linalg.inv(B))>1e-9:return False
 return True
accepted=0;bestdet=-1e9;bestoff=-1e9;best=None
for step in range(20000):
 B=A.copy();i,j=rng.integers(0,5,2);B[i,j]+=rng.normal()*rng.choice([.05,.2,1.])
 if qualify(B):
  accepted+=1;A=B
  det=np.linalg.det(A);inv=np.linalg.inv(A);off=max(inv[i,j] for i in range(5) for j in range(5) if i!=j)
  if det>bestdet:bestdet=float(det)
  if off>bestoff:bestoff=float(off);best=A.tolist()
  if det>=0 or off>1e-6:break
 if step%1000==999:A=BASE.copy()
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),steps=step+1,accepted=accepted,max_det=bestdet,max_inverse_offdiagonal=bestoff,best=best,diagnostic_only=True,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(p/'diagnostic5.json').write_text(json.dumps(r,indent=2));print(r)
