from pathlib import Path
from math import factorial,comb,prod
import json,time
L=Path(__file__).resolve().parent

def partitions(n,cap=None):
 if n==0:yield ();return
 for k in range(min(n,cap or n),1-1,-1):
  for p in partitions(n-k,k):yield (k,)+p

def hooks(p):
 return prod(p[i]-j+sum(q>j for q in p[i+1:]) for i in range(len(p)) for j in range(p[i]))

def row(n):
 cs=[0]*n
 for p in partitions(n):
  f=factorial(n)//hooks(p);mu=p[1:];h=hooks(mu)
  contents=[j-i for i,r in enumerate(mu) for j in range(r)]
  for m in range(1,n):
   numerator=prod(m-1+c for c in contents)
   assert numerator%h==0
   cs[m]+=f*(numerator//h)
 a=[];diff=cs[:]
 while diff:
  a.append(diff[0]);diff=[y-x for x,y in zip(diff,diff[1:])]
 return a,cs
out=[];start=time.monotonic()
for n in range(2,37):
 a,c=row(n)
 bad=[k for k in range(2,n-1) if a[k]**2<a[k-1]*a[k+1]]
 modes=[k for k,x in enumerate(a) if x==max(a)]
 item={'n':n,'a':a,'logconcavity_failures':bad,'modes':modes,'claimed_mode':(n+1)//2}
 out.append(item)
 print(n,modes,'LC failures',bad,flush=True)
 if bad or (n+1)//2 not in modes:break
(L/'checks.json').write_text(json.dumps({'rows':out,'wall_seconds':time.monotonic()-start},indent=2))
