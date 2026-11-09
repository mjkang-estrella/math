import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
from math import comb
from pathlib import Path
import json
C=lambda n,i:comb(n,i) if 0<=i<=n else 0
out={'proof':False,'cases':0,'failure':None,'rows':[1000,10000,1000000,1000000000000],'edge_distances':'0..100 at both ends'}
for r in out['rows']:
 for j in list(range(101))+list(range(2*r-98,2*r+3)):
  # All omitted i have four zero bases; padding both sides equally does not change prefixes.
  inds=range(max(0,j-r-2),min(r+1,j)+1)
  p=[(r+2)*C(r,i)*C(r+2,j-i) for i in inds]+[(r+1)*C(r,i)*C(r+1,j-i) for i in inds]
  q=[(r+2)*C(r,i)*C(r+1,j-i) for i in inds]+[(r+1)*C(r+1,i)*C(r+1,j-i) for i in inds]
  s=0
  for k,(a,b) in enumerate(zip(sorted(p,reverse=True),sorted(q,reverse=True)),1):
   s+=a*a-b*b
   if s<0:out['failure']={'r':r,'j':j,'prefix':k,'difference':s};break
  out['cases']+=1
  if out['failure']:break
 if out['failure']:break
out['status']='route_falsified' if out['failure'] else 'finite_PASS_only'
Path(__file__).with_name('sparse.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
