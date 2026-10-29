import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
import numpy as np,json
from pathlib import Path
H=np.ones((1,1))
for i in range(4):H=np.block([[H,H],[H,-H]])
U=H/4;B=np.block([[np.eye(16),U],[U.T,np.eye(16)]]);mx=0;rng=np.random.default_rng(333)
for i in range(1000):
 p=rng.permutation(32);L=np.tril(B[np.ix_(p,p)],-1);v=np.linalg.norm(L,2)
 if v>mx:mx=v;arg=p.copy()
L=np.tril(B[np.ix_(arg,arg)],-1);u,s,vh=np.linalg.svd(L);x=np.rint(vh[0]*1000).astype(int)
r={'rank':16,'max_norm_sampled':float(mx),'max_order':arg.tolist(),'witness':x.tolist(),'witness_rayleigh':float(np.linalg.norm(L@x)**2/np.linalg.norm(x)**2),'sampled_permutations':1000,'diagnostic_only':True};Path(__file__).with_name('hadamard-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
