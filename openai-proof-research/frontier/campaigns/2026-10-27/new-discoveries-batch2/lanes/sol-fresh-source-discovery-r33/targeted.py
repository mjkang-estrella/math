import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
import numpy as np,itertools,json
from pathlib import Path
H=np.array([[1,1,1,1],[1,-1,1,-1],[1,1,-1,-1],[1,-1,-1,1]])/2
B=np.block([[np.eye(4),H],[H.T,np.eye(4)]]);mx=0;mn=100
for p in itertools.permutations(range(8)):
 L=np.tril(B[np.ix_(p,p)],-1);v=np.linalg.norm(L,2)
 if v>mx:mx=v;arg=p
 mn=min(mn,v)
L=np.tril(B[np.ix_(arg,arg)],-1);u,s,vh=np.linalg.svd(L);x=np.rint(vh[0]*100).astype(int)
r={'matrix':B.tolist(),'max_norm':float(mx),'min_norm':float(mn),'max_order':list(arg),'witness':x.tolist(),'witness_rayleigh':float(np.linalg.norm(L@x)**2/np.linalg.norm(x)**2),'diagnostic_only':True,'permutations':40320};Path(__file__).with_name('targeted-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
