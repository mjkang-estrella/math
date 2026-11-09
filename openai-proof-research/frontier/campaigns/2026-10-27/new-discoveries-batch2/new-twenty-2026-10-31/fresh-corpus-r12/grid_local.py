from itertools import combinations,product
import json
from pathlib import Path
p=Path(__file__).parent
out=[]
for w in [3,4,5,6]:
 bad=[]
 for t in combinations(range(3*w),3):
  xy=[divmod(i,3) for i in t];a,b,c=xy
  if (b[0]-a[0])*(c[1]-a[1])==(c[0]-a[0])*(b[1]-a[1]):continue
  d=[(u[0]-v[0])**2+(u[1]-v[1])**2 for u,v in combinations(xy,2)]
  if len(set(d))<3:bad.append(sum(1<<i for i in t))
 good=[s for s in range(1<<(3*w)) if all(s&t!=t for t in bad)]
 trans={}
 mask=(1<<(3*(w-1)))-1
 for s in good:trans.setdefault(s&mask,[]).append((s>>3,(s>>(3*(w-1))).bit_count()))
 dp={s:s.bit_count() for s in range(1<<(3*(w-1))) if all(s&t!=t for t in bad)}
 vals=[]
 for n in range(w,51):
  nd={}
  for s,v in dp.items():
   for t,c in trans.get(s,[]):nd[t]=max(nd.get(t,-10000),v+c)
  dp=nd;vals.append([n,max(dp.values())])
 row={'window_rows':w,'states':len(trans),'maxima':vals};out.append(row);print(row,flush=True)
(p/'grid-local-diagnostics.json').write_text(json.dumps(out,indent=2))
