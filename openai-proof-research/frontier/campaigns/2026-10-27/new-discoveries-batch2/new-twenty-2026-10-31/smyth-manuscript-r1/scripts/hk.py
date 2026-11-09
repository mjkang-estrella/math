from pathlib import Path
import runpy,json
from collections import deque
a=runpy.run_path(str(Path(__file__).with_name('audit.py')));comps=a['comps'];rearr=a['rearr'];dom=a['dom'];R=a['R']
X=[rearr(u+v) for u in comps(3,19) for v in comps(2,20)]
Y=[rearr(u+v) for u in comps(3,20) for v in comps(2,19)]
groups={}
for j,q in enumerate(Y):groups.setdefault(q,[]).append(j)
nb={p:tuple(j for q,js in groups.items() if dom(p,q) for j in js) for p in set(X)}
adj=[nb[p] for p in X];L=[-1]*len(X);M=[-1]*len(Y)
while True:
 d=[-1]*len(X);q=deque()
 for i in range(len(X)):
  if L[i]<0:d[i]=0;q.append(i)
 found=False
 while q:
  u=q.popleft()
  for v in adj[u]:
   w=M[v]
   if w<0:found=True
   elif d[w]<0:d[w]=d[u]+1;q.append(w)
 if not found:break
 it=[0]*len(X)
 def augment(u):
  while it[u]<len(adj[u]):
   v=adj[u][it[u]];it[u]+=1;w=M[v]
   if w<0 or (d[w]==d[u]+1 and augment(w)):
    L[u]=v;M[v]=u;return True
  d[u]=-1;return False
 for u in range(len(X)):
  if L[u]<0:augment(u)
assert all(v<0 or (M[v]==u and dom(X[u],Y[v])) for u,v in enumerate(L))
out={'maximum':sum(v>=0 for v in L),'edges':sum(map(len,adj)),'method':'element-level Hopcroft-Karp with type-shared adjacency'}
assert out['maximum']==4407
(R/'audit-hk.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
