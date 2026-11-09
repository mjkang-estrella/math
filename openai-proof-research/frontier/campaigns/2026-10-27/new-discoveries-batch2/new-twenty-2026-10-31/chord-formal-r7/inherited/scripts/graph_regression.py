from itertools import combinations,permutations
from pathlib import Path
import json
rows=[]
for n in range(7):
 edges=list(combinations(range(n),2)); nonbip=0; triangles=0; windows=0
 for mask in range(1<<len(edges)):
  adj=[set() for _ in range(n)]
  for k,(i,j) in enumerate(edges):
   if mask>>k&1: adj[i].add(j); adj[j].add(i)
  color={}; bip=True
  for i in range(n):
   if i in color: continue
   color[i]=0; todo=[i]
   while todo:
    a=todo.pop()
    for b in adj[a]:
     if b not in color: color[b]=1-color[a]; todo.append(b)
     elif color[a]==color[b]: bip=False
  if bip: continue
  nonbip+=1
  tri=any(b in adj[a] and c in adj[a] and c in adj[b] for a,b,c in combinations(range(n),3))
  if tri: triangles+=1; continue
  win=any(all(p[i+1] in adj[p[i]] for i in range(4)) for p in permutations(range(n),5))
  assert win,(n,mask)
  windows+=1
 rows.append(dict(vertices=n,graphs=1<<len(edges),nonbipartite=nonbip,triangle=triangles,triangle_free_window=windows))
result=dict(rows=rows,numerical_only=True)
Path('graph-regression.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
