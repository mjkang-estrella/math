import numpy as np,itertools,json,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(45,45));resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
def rho2(d):
 a=np.minimum.outer(d,d).astype(float);return float(np.linalg.eigvalsh(a)[-1])
rows=[];count=0
for p in range(2,8):
 for q in range(p,11):
  allowed={}
  for s in range(1,p+1):
   for t in range(1,q+1):
    for k in range(min(s,t)+1):
     e=s*t-k
     if e<2:continue
     # delete from vertex in the larger part
     d=([t]*(s-1)+[t-k]) if s>=t else ([s]*(t-1)+[s-k])
     v=rho2(d);allowed[e]=max(allowed.get(e,0),v)
  for a in itertools.combinations_with_replacement(range(q+1),p):
   d=tuple(reversed(a));e=sum(d)
   if not 1<e<p*q:continue
   count+=1;v=rho2(d)
   if v>allowed.get(e,0)+1e-8:rows.append({'p':p,'q':q,'e':e,'row_degrees':d,'rho_squared_float':v,'best_refined_candidate_rho_squared_float':allowed.get(e),'scope':'numerical diagnostic only'})
print(count,len(rows));print(rows[:8]);Path(__file__).with_name('spectral-diagnostic.json').write_text(json.dumps({'count':count,'violations':rows},indent=2))
