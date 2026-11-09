import os
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(45,45))
from math import comb
from itertools import accumulate
from pathlib import Path
import json,random,time
root=Path(__file__).resolve().parent
out={'proof':False,'memory_bytes':536870912,'cpu_seconds':45,'cases':0,'failure':None,'local_failure':None}
def row(n):return [comb(n,i) for i in range(n+1)]
def lists(r,j):
 rows=[row(r+t) for t in range(3)]
 def c(t,i):return rows[t][i] if 0<=i<len(rows[t]) else 0
 p=[(r+2)*c(0,i)*c(2,j-i) for i in range(r+3)]+[(r+1)*c(0,i)*c(1,j-i) for i in range(r+3)]
 q=[(r+2)*c(0,i)*c(1,j-i) for i in range(r+3)]+[(r+1)*c(1,i)*c(1,j-i) for i in range(r+3)]
 return sorted(p,reverse=True), sorted(q,reverse=True)
random.seed(1729)
pairs=[(r,j) for r in range(61,151) for j in range(2*r+3)]
pairs +=[(r,j) for r in (200,300,500,800,1000) for j in sorted(set([0,1,2,3,4,5,10,r//4,r//2,r,r+1,2*r,2*r+1,2*r+2]+[random.randrange(2*r+3) for _ in range(12)]))]
for r,j in pairs:
 p,q=lists(r,j)
 for k,(a,b) in enumerate(zip(accumulate(t*t for t in p),accumulate(t*t for t in q)),1):
  if a<b:
   out['failure']={'r':r,'j':j,'prefix':k,'difference':a-b};break
 out['cases']+=1
 if out['failure']:break
# Test symmetrized local grouping, including zero endpoints; no proof inferred.
for n in range(1,30):
 for j in range(2*n+1):
  for i in range(max(0,j-n),min(n,j)+1):
   k=j-i
   if i>k:continue
   C=lambda n,i:comb(n,i) if 0<=i<=n else 0
   inds=[i,k] if i!=k else [i]
   p=[(n+1)*C(n-1,t)*C(n+1,j-t) for t in inds]+[n*C(n-1,t)*C(n,j-t) for t in inds]
   q=[(n+1)*C(n-1,t)*C(n,j-t) for t in inds]+[n*C(n,t)*C(n,j-t) for t in inds]
   if sum(t*t for t in p)<sum(t*t for t in q):
    out['local_failure']={'n':n,'j':j,'i':i,'k':k,'P':p,'N':q,'squared_total_difference':sum(t*t for t in p)-sum(t*t for t in q)};break
  if out['local_failure']:break
 if out['local_failure']:break
out['status']='route_falsified' if out['failure'] else 'finite_PASS_only'
(root/'exploration.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
