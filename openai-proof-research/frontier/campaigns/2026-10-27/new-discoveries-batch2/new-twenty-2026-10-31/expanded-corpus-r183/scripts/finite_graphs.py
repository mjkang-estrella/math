from pathlib import Path
from itertools import combinations
import json
D=Path(__file__).resolve().parents[1];rows=[]
for n in range(1,7):
 pairs=list(combinations(range(n),2));count=gapfree=nonisolated=0
 for mask in range(1<<len(pairs)):
  adj=[[] for _ in range(n)];edges=[]
  for k,(u,v) in enumerate(pairs):
   if mask>>k&1:adj[u].append(v);adj[v].append(u);edges.append((u,v))
  order=[-1]*n;parent=[-1]*n;orient=set();tree=set();components=0
  def dfs(v):
   order[v]=sum(x>=0 for x in order)
   for w in adj[v]:
    if order[w]<0:parent[w]=v;tree.add(tuple(sorted((v,w))));orient.add((v,w));dfs(w)
    elif w!=parent[v] and order[w]<order[v]:orient.add((v,w))
  for v in range(n):
   if order[v]<0:components+=1;dfs(v)
  chords=[e for e in edges if e not in tree]
  assert len(chords)==len(edges)-n+components
  for u,v in chords:
   if order[u]<order[v]:u,v=v,u
   assert (u,v) in orient
   q=u
   while q!=v:
    assert parent[q]>=0 and (parent[q],q) in orient
    q=parent[q]
  count+=1
  ok=True
  for u,v in edges:
   for x,y in edges:
    if len({u,v,x,y})==4 and not any(b in adj[a] for a in (u,v) for b in (x,y)):ok=False;break
   if not ok:break
  gapfree+=ok
  nonisolated+=ok and all(adj)
 rows.append({'vertices':n,'all_labelled_graphs':count,'directed_fundamental_basis_failures':0,'gap_free':gapfree,'gap_free_no_isolates':nonisolated,'matching_bound':n//2})
 print(rows[-1],flush=True)
(D/'outputs/finite-graphs.json').write_text(json.dumps(rows,indent=2)+'\n')
