import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20))
from math import comb
from pathlib import Path
import json
C=lambda n,i:comb(n,i) if 0<=i<=n else 0
out={}
for r in range(101):
 for j in range(2*r+3):
  groups=[[scale*C(t,i)*C(u,j-i) for i in range(r+3)] for scale,t,u in [(r+2,r,r+2),(r+1,r,r+1),(r+2,r,r+1),(r+1,r+1,r+1)]]
  groups=[sorted(g,reverse=True) for g in groups]
  for k,v in enumerate(zip(*groups)):
   p,q=sorted(v[:2],reverse=True),sorted(v[2:],reverse=True)
   if max(p)<max(q) or sum(t*t for t in p)<sum(t*t for t in q):
    out={'failure':{'r':r,'j':j,'rank':k,'P':p,'N':q,'sum_square_difference':sum(t*t for t in p)-sum(t*t for t in q)}};break
  if out:break
 if out:break
Path(__file__).with_name('blocks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
