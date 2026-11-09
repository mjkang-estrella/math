"""Finite diagnostics only; full metric LP, not a proof of a universal bound."""
from pathlib import Path
from itertools import permutations,combinations,product
from fractions import Fraction as F
import json,random
import numpy as np
from scipy.optimize import linprog
O=Path(__file__).resolve().parent
ranks=list(permutations(range(3)));rng=random.Random(526)
def run(count,s):
 active=[i for i,c in enumerate(count) if c];n=sum(count);k=len(active);N=3+k
 edges=list(combinations(range(N),2));idx={e:i for i,e in enumerate(edges)};M=len(edges)
 def row(terms):
  a=np.zeros(M)
  for x,y,v in terms:
   if x!=y:a[idx[tuple(sorted((x,y)))]]+=v
  return a
 A=[]
 for x,y,z in permutations(range(N),3):
  if x<y:A.append(row([(x,y,1),(x,z,-1),(z,y,-1)]))
 for j,t in enumerate(active):
  for x,y in zip(ranks[t],ranks[t][1:]):A.append(row([(3+j,x,1),(3+j,y,-1)]))
 q=[sum(F(count[t])*s[ranks[t].index(c)] for t in range(6))/(n*sum(s)) for c in range(3)]
 out=[]
 for a in range(3):
  nbr=[set(ranks[t][ranks[t].index(a):]) for t in active]
  if any(sum(F(count[active[j]],n) for j in range(k) if mask>>j&1)>sum(q[c] for c in set().union(*(nbr[j] for j in range(k) if mask>>j&1))) for mask in range(1,1<<k)):continue
  for b in range(3):
   if a==b:continue
   obj=row([(3+j,a,-count[t]) for j,t in enumerate(active)])
   eq=row([(3+j,b,count[t]) for j,t in enumerate(active)])
   res=linprog(obj,A_ub=A,b_ub=np.zeros(len(A)),A_eq=[eq],b_eq=[1],bounds=(0,None),method='highs',options={'time_limit':2,'threads':1})
   if res.success:out.append((float(-res.fun),a,b))
 return out
records=[];best=None
for s in [(F(1),F(u,4),F(v,4)) for u in range(5) for v in range(u+1)]:
 mx=0;arg=None;tested=0
 # Source lower witness plus heterogeneous profiles; exact Hall, floating metric LP.
 T=sum(s)-s[-1];den=T.denominator;num=T.numerator
 cases=[[den,0,0,0,num,0]]+[[rng.randrange(6) for _ in range(6)] for z in range(90)]
 for count in cases:
  if not sum(count):continue
  vals=run(count,s);tested+=1
  if vals and max(vals)[0]>mx:mx,a,b=max(vals);arg=[count,a,b]
  if mx>float(1+2*T)+1e-7:break
 records.append({'s':list(map(str,s)),'target':str(1+2*T),'max_float':mx,'arg':arg,'profiles':tested})
(O/'check-results.json').write_text(json.dumps({'seed':526,'scope':'m=3 only, exact rational Hall test, floating full pseudometric LP; no proof/clearance','records':records},indent=2))
print(json.dumps(records,indent=2))
