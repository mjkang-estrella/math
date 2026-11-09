"""Bounded exploratory probe, not an E0_2 classifier or proof."""
import os,resource
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'): os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(25,)*2)
import numpy as np,json
from pathlib import Path
rng=np.random.default_rng(73129)
counts={'trials':0,'invertible_borders':0,'positive_diagonal':0,'pair_E0':0}
best=None
for n in (6,8,10):
 for _ in range(2000):
  counts['trials']+=1
  D=rng.integers(10,21,(n,n)); D=np.triu(D,1);D=D+D.T
  W=np.zeros((n+1,n+1));W[:n,:n]=D;W[:n,n]=1;W[n,:n]=1
  try: A=2*np.linalg.inv(W)[:n,:n]
  except np.linalg.LinAlgError:continue
  if np.linalg.cond(W)>1e10:continue
  counts['invertible_borders']+=1
  dg=np.diag(A)
  if min(dg)<=1e-9:continue
  counts['positive_diagonal']+=1
  score=min(A[i,j]+np.sqrt(dg[i]*dg[j]) for i in range(n) for j in range(i))
  if best is None or score>best['score']:best={'score':float(score),'D':D.tolist()}
  if score>=1e-9: counts['pair_E0']+=1
out={'counts':counts,'best':best,'scope':'Numerical fixed finite probe only; exact verification needed for any witness.'}
Path(__file__).with_name('metric-probe.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
