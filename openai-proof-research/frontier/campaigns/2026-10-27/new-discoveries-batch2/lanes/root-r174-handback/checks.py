"""Independent shadow extraction controls, not a proof of the source conjecture."""
import itertools as it,json,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
def rank(v):return tuple(sum(w<x for w in v) for x in v)
def shadow(v,k):return {rank(x) for x in it.combinations(v,k)}
def family(p,i,j,sign,t):
 a=[x if x<j else x+t for x in p];b=list(range(j,j+t))[::sign];return a[:i]+b+a[i:]
rows=[]
for k in [3,4,5,6]:
 count=0
 # Deterministic diverse cores and cells; two independent shadow constructions.
 for a,p in enumerate(it.permutations(range(k))):
  if a%max(1,k*3):continue
  for i,j in [(0,0),(0,k),(k,0),(k,k),(k//2,k//2)]:
   for sign in [-1,1]:
    s=shadow(family(p,i,j,sign,k),k)
    assert s==shadow(family(p,i,j,sign,k+1),k)
    # Any large monotone block may be collapsed to its selected entries.
    alt=set()
    for r in range(k+1):
     for indices in it.combinations(range(k),k-r):
      core=[p[x] for x in indices];pos=sum(x<i for x in indices)
      t=max(1,r);v=family(core,pos,j,sign,t)
      if r==0:v=core
      alt.add(rank(v))
    assert s==alt
    count+=1
 rows.append(dict(k=k,stabilization_controls=count))
result=dict(controls=rows,scope='Independent selected-shadow and stabilization controls only; no all-k proof; full scan outputs preserved separately')
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
