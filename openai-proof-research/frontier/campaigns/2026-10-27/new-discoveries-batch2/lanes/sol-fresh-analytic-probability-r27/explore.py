import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,math
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(40)
import numpy as np
s=0.;rows=[]
for j in range(100):
 n=np.arange(j*1000000+1,(j+1)*1000000+1,dtype=np.float64)
 s+=np.sum(np.exp(n*np.log((2+np.sin(n))/3))/n)
 if j in [0,9,99]:
  row=dict(N=(j+1)*1000000,sum=float(s),heuristic_limit=float(s+math.sqrt(6/math.pi)/math.sqrt((j+1)*1000000)));rows.append(row);print(row,flush=True)
from pathlib import Path
Path(__file__).with_name('explore-output.json').write_text(json.dumps({'diagnostic_only':True,'rows':rows},indent=2))
