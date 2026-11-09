from fractions import Fraction as F
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json,sys
@lru_cache(None)
def partitions(n,m):
 if n==0:return ((),)
 return tuple((k,)+p for k in range(min(n,m),0,-1) for p in partitions(n-k,k))
def hooks(p):
 return [(p[i]-j-1,sum(q>j for q in p[i+1:])) for i in range(len(p)) for j in range(p[i])]
def subparts(p):
 def rec(i,m):
  if i==len(p):yield ();return
  for j in range(min(m,p[i])+1):
   for tail in rec(i+1,j):yield (j,)+tail
 return rec(0,p[0] if p else 0)
out=[]
for n in range(int(sys.argv[1])+1):
 rows=[]
 for tau in partitions(n,n):
  h=hooks(tau);lo=max((F(l,a+l+1) for a,l in h),default=F(0));hi=min((F(l+1,a+l+1) for a,l in h),default=F(1))
  if lo>=hi:continue
  t=(lo+hi)/2;poly=Counter()
  for mu in subparts(tau):
   sim=sum(F(l,a+l+1)<=t<F(l+1,a+l+1) for a,l in hooks(mu));poly[n-sum(mu),sim]+=1
  symmetric=all(v==poly[b,a] for (a,b),v in list(poly.items()));bad=[]
  for d in range(n+1):
   for b in range(d//2+1):
    c=poly[d-b,b]-(poly[d-b+1,b-1] if b else 0)
    if c<0:bad.append((d-b,b,c))
  rows.append({'tau':tau,'subpartitions':sum(poly.values()),'symmetric':symmetric,'negative_schur':bad})
 rec={'size':n,'triangular_partitions':len(rows),'rows':rows};out.append(rec);print(n,len(rows),sum(not r['symmetric'] or bool(r['negative_schur']) for r in rows),flush=True)
Path('outputs/schur.json').write_text(json.dumps(out,indent=2)+'\n')
