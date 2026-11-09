import os
for v in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[v]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
import numpy as np,json,datetime
from pathlib import Path
rng=np.random.default_rng(373375)
p=Path(__file__).parent
A=np.array([[1,.5,-1,-1],[1/3,1,-1,-1],[-1,-1,1,0],[-1,-1,0,1.]])
def qualify(A):
 for k in range(4):
  ix=[i for i in range(4) if i!=k];B=A[np.ix_(ix,ix)]
  if np.linalg.det(B)>=-1e-7:return False
  if np.max(np.linalg.inv(B))>1e-9:return False
 return np.min(np.diag(A))>=0
# The triple-inverse test implies every pair has nonnegative determinant.
# Together with nonnegative diagonal, this implies pair semimonotonicity.
accepted=0;bestdet=-1e9;bestoff=-1e9;best=None
for step in range(30000):
 B=A.copy();i,j=rng.integers(0,4,2);B[i,j]+=rng.normal()*rng.choice([.05,.2,1.])
 if qualify(B):
  accepted+=1;A=B
  det=np.linalg.det(A);inv=np.linalg.inv(A);off=max(inv[i,j] for i in range(4) for j in range(4) if i!=j)
  if det>bestdet:bestdet=float(det)
  if off>bestoff:bestoff=float(off);best=A.tolist()
  if det>=0 or off>1e-6:break
 if step%1000==999:A=np.array([[1,.5,-1,-1],[1/3,1,-1,-1],[-1,-1,1,0],[-1,-1,0,1.]])
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),steps=step+1,accepted=accepted,max_det=bestdet,max_inverse_offdiagonal=bestoff,best=best,diagnostic_only=True,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
(p/'diagnostic.json').write_text(json.dumps(r,indent=2));print(r)
