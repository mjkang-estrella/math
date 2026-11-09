from pathlib import Path
from itertools import product
import os,json,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).parent;t=time.monotonic()
def patterns(lam,mu,nu,k):
 top=tuple(k*x for x in lam);bot=tuple(k*x for x in mu);targets=[sum(bot)]
 for x in nu:targets.append(targets[-1]+k*x)
 def rec(rows):
  a=rows[-1];i=len(rows)
  if i==len(nu):
   if all(top[j]>=a[j] and (j+1==len(a) or a[j]>=top[j+1]) for j in range(len(a))):yield tuple(reversed(rows+[top]))
   return
  # Exact interlacing: b_j >= a_j >= b_{j+1}; row sum is fixed.
  for b in product(*(range(a[j],top[j]+1) if j==0 else range(a[j],min(top[j],a[j-1])+1) for j in range(len(a)))):
   if sum(b)==targets[i]:yield from rec(rows+[b])
 return list(rec([bot]))
reports=[]
for lam,mu,nu in [((3,2),(0,0),(2,2,1)),((4,3,1),(1,0,0),(3,2,2))]:
 base=sorted(patterns(lam,mu,nu,1)); rr=[]
 for k in range(1,7):
  q=patterns(lam,mu,nu,k); scaled=[tuple(tuple(k*v for v in row) for row in G) for G in base]
  fibres=[0]*len(base)
  for H in q:
   idx=max(i for i,G in enumerate(scaled) if G<=H);fibres[idx]+=1
  cum=[sum(H<=G for H in q) for G in scaled]
  assert all(fibres[i]==cum[i+1]-cum[i] for i in range(len(base)-1))
  assert fibres[-1]==1
  rr.append({'k':k,'patterns':len(q),'fibres':fibres,'cumulative':cum})
 reports.append({'lambda':lam,'mu':mu,'nu':nu,'base_patterns':base,'values':rr,'scope':'two fixed diagnostic shapes, no polynomiality inference'})
(p/'diagnostics.json').write_text(json.dumps({'GT':reports,'elapsed_seconds':time.monotonic()-t,'max_cpus':2},indent=2));print('seconds',time.monotonic()-t,'base counts',[len(x['base_patterns']) for x in reports])
