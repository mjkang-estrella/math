from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json
r=Path(__file__).resolve().parents[1];d=json.loads((r/'work/marginal-exploration.json').read_text());x=list(map(F,d['x']));ts=d['all_trees'];ids=[i for i,z in enumerate(d['thinness']) if F(z)<=F(5,3)]
def solve(cols):
 a=[[F(t[i]) for t in cols]+[x[i]] for i in range(len(x))]+[[F(1)]*(len(cols)+1)];n=len(cols);row=0;piv=[]
 for j in range(n):
  k=next((k for k in range(row,len(a)) if a[k][j]),None)
  if k is None:continue
  a[row],a[k]=a[k],a[row];v=a[row][j];a[row]=[z/v for z in a[row]]
  for k in range(len(a)):
   if k!=row:
    v=a[k][j];a[k]=[z-v*y for z,y in zip(a[k],a[row])]
  piv.append(j);row+=1
 if any(not any(line[:-1]) and line[-1] for line in a) or len(piv)<n:return None
 v=[F(0)]*n
 for k,j in enumerate(piv):v[j]=a[k][-1]
 return v if all(z>=0 for z in v) else None
for k in range(1,7):
 for iset in combinations(ids,k):
  v=solve([ts[i] for i in iset])
  if v is not None:
   out={'indices':iset,'weights':list(map(str,v)),'exact_threshold':'5/3'};(r/'work/marginal-decomposition.json').write_text(json.dumps(out,indent=2)+'\n');print(out);raise SystemExit
