from itertools import combinations,product
from fractions import Fraction as F
from pathlib import Path
import json,random
ROOT=Path(__file__).resolve().parents[1]
def trees(n,edges):
 out=[]
 for inds in combinations(range(len(edges)),n-1):
  p=list(range(n))
  def root(u):
   while p[u]!=u:u=p[u]
   return u
  good=True
  for i in inds:
   u,v=map(root,edges[i])
   if u==v:good=False;break
   p[u]=v
  if good:out.append(tuple(int(i in inds) for i in range(len(edges))))
 return out
n=4;edges=list(combinations(range(n),2));ts=trees(n,edges)
cuts=[tuple(int(bool(s>>u&1)!=bool(s>>v&1)) for u,v in edges) for s in range(1,1<<(n-1))]
loads=[[sum(a*b for a,b in zip(t,c)) for c in cuts] for t in ts]
costs=list(product(range(2),repeat=len(edges)))
best=None
for ia,ib in combinations(range(len(ts)),2):
 for w in [1,2,3,4]:
  den=5;x=[F(w*a+(den-w)*b,den) for a,b in zip(ts[ia],ts[ib])]
  if not all(x):continue
  mass=[sum(a*b for a,b in zip(x,c)) for c in cuts]
  ratios=[max(F(z)/d for z,d in zip(row,mass)) for row in loads]
  alpha=min(ratios)
  for c in costs:
   cx=sum(a*b for a,b in zip(x,c));cheap=[j for j,t in enumerate(ts) if sum(a*b for a,b in zip(t,c))<=cx]
   bound=min(ratios[j] for j in cheap)
   if bound>alpha and (best is None or bound/alpha>best[0]):
    best=(bound/alpha,{'n':n,'edges':edges,'tree_a':ts[ia],'tree_b':ts[ib],'weight_a':str(F(w,den)),'x':list(map(str,x)),'cost':c,'fractional_cost':str(cx),'existence_threshold':str(alpha),'necessary_decomposition_threshold':str(bound),'all_trees':ts,'thinness':list(map(str,ratios)),'costs':[sum(a*b for a,b in zip(t,c)) for t in ts]})
print(json.dumps(best[1] if best else None,indent=2))
(ROOT/'work/marginal-exploration.json').write_text(json.dumps(best[1] if best else None,indent=2)+'\n')
