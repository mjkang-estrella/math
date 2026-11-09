from collections import deque,Counter
from fractions import Fraction
for n in [8,9,12]:
 edges=[(0,1),(0,2),(0,3),(1,2),(1,3)]+[(0,k) for k in range(4,n)]
 adj=[[] for k in range(n)]
 for a,b in edges:adj[a].append(b);adj[b].append(a)
 dist=[]
 for a in range(n):
  ds=[n+1]*n;ds[a]=0;q=deque([a])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if ds[v]>ds[u]+1:ds[v]=ds[u]+1;q.append(v)
  dist.append(ds)
 pairs=[]
 for a,b in edges:
  u=sum(dist[a][k]<dist[b][k] for k in range(n));v=sum(dist[b][k]<dist[a][k] for k in range(n));pairs.append((u,v))
 expected=Counter({(n-3,1):1,(n-2,1):2,(2,1):2,(n-1,1):n-4})
 assert Counter(pairs)==expected
 print('n',n,'exact distance-count pairs',dict(Counter(pairs)),'radicands',[(p,str(Fraction(p[0]+p[1]-2,p[0]*p[1]))) for p in Counter(pairs)])
print('Diagnostic agreement with ordinary H formula only; not a Lean graph/index certificate; correction and public resolution receive zero credit.')
