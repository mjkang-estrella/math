from research import *
from itertools import combinations,product
from collections import deque
def literal(n,vc,ec,k):
 edges=list(combinations(range(n),2));N=n+len(edges);adj=[[] for _ in range(N)]
 for z,(u,v) in enumerate(edges,n):
  for x in [u,v]:adj[x].append(z);adj[z].append(x)
 colors=vc+ec
 if any(colors[x]==colors[y] for x in range(N) for y in adj[x]):return False
 def dist(u,v,c=None):
  q=deque([u]);d={u:0}
  while q:
   x=q.popleft()
   if x==v:return d[x]
   for y in adj[x]:
    if y not in d and (y==v or c is None or colors[y]!=c):d[y]=d[x]+1;q.append(y)
  return None
 return all(dist(u,v)==dist(u,v,colors[u]) for u,v in combinations(range(N),2) if colors[u]==colors[v])
def reduced(n,vc,ec):
 edges=list(combinations(range(n),2));d=dict(zip(edges,ec))
 return all(c!=vc[u] and c!=vc[v] for (u,v),c in d.items()) and all(len({d[e] for e in combinations(q,2)})>1 for q in combinations(range(n),4))
def run():
 counts=[]
 for n,k in [(2,2),(3,2),(4,2),(5,2),(4,3)]:
  total=valid=0
  for c in product(range(k),repeat=n+n*(n-1)//2):
   vc,ec=c[:n],c[n:];a=literal(n,vc,ec,k);b=reduced(n,vc,ec);assert a==b,(n,k,c);total+=1;valid+=a
  counts.append({'n':n,'k':k,'colorings':total,'valid':valid})
 # Three four-vertex blocks, common cross color zero. Every global merge fails.
 n=12;d={};pairs=[(1,2),(1,3),(2,3)]
 for u,v in combinations(range(n),2):
  d[u,v]=0 if u//4!=v//4 else (pairs[u//4][0] if (u%4,v%4)==(0,1) else pairs[u//4][1])
 vc=tuple(next(c for c in range(4) if c not in {d[min(u,v),max(u,v)] for v in range(n) if v!=u}) for u in range(n));ec=tuple(d.values())
 assert literal(n,vc,ec,4) and reduced(n,vc,ec)
 witnesses=[]
 for a,b in combinations(range(4),2):
  merged={e:(a if c==b else c) for e,c in d.items()}
  q=next(q for q in combinations(range(n),4) if len({merged[e] for e in combinations(q,2)})==1)
  witnesses.append({'merge':[a,b],'monochromatic_K4':q})
 save('check-results.json',{'utc':utc(),'equivalence_checks':counts,'merge_obstruction':{'n':12,'vertex_missing_colors':vc,'edge_colors':ec,'witnesses':witnesses},'claim':'finite translation tests and method obstruction only; no all-n source proof'})
 print(json.dumps(counts))
if __name__=='__main__':run()
