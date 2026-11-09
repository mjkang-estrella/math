#!/usr/bin/env python3
import os,resource
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
_hard=resource.getrlimit(resource.RLIMIT_CPU)[1]
_cpu=55 if _hard==resource.RLIM_INFINITY else min(55,_hard)
resource.setrlimit(resource.RLIMIT_CPU,(_cpu,_cpu))
import json,datetime,time
from pathlib import Path
from itertools import combinations_with_replacement
from functools import lru_cache
OUT=Path(__file__).with_name('checks.json')
report={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':{'AS_MiB':512,'CPU_seconds':55,'threads':1},'cases':[]}
def save():OUT.write_text(json.dumps(report,indent=2)+'\n')
def polynomial(n,r):
 parts=[tuple(reversed(t)) for t in combinations_with_replacement(range(n+1),r)]
 def sign(mu,nu):
  free=[0]*r
  for j in range(n):
   rows=[i for i in range(r) if mu[i]<=j<nu[i]]
   if len(rows)>2:return 0
   if len(rows)==1:free[rows[0]]+=1
  return 0 if any(x%3==2 for x in free) else (-1)**sum(x%3==1 for x in free)
 @lru_cache(None)
 def go(l,mu):
  if l==r:return {():1} if mu==(n,)*r else {}
  out={}
  for nu in parts:
   if nu[l]!=n or any(a>b for a,b in zip(mu,nu)):continue
   v=sign(mu,nu)
   if not v:continue
   size=sum(nu)-sum(mu)
   for tail,c in go(l+1,nu).items():
    key=(size,)+tail;out[key]=out.get(key,0)+v*c
  return {e:c for e,c in out.items() if c}
 return go(0,(0,)*r)
if __name__=='__main__':
 try:
  for n,r in [(1,2),(2,2),(3,2),(4,2),(1,4),(2,4),(3,4),(4,4),(1,6),(2,6),(3,6),(4,6)]:
   t=time.monotonic();p=polynomial(n,r);neg=sorted((e,c) for e,c in p.items() if c<0)
   case={'n':n,'r':r,'terms':len(p),'negative_count':len(neg),'seconds':time.monotonic()-t,'first_negative':neg[:1]}
   if (n,r)==(4,6):case['old_profile_coefficient']=p.get((4,7,4,6,2,1),0)
   report['cases'].append(case);save();print(case,flush=True)
   if neg:
    report['negative_witness']={'n':n,'r':r,'content':neg[0][0],'coefficient':neg[0][1]};break
  report['status']='PASS exact diagnostic; no source theorem proved'
 except BaseException as e:
  report['failure']=repr(e);save();raise
 save()
