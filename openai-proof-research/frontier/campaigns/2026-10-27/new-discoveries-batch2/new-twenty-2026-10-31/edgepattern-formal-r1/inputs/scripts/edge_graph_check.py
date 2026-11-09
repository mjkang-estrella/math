import itertools as it,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];x=json.loads((D/'outputs/edge-certificate.json').read_text());adj=x['graph']['adj'];n=len(adj);edges=[(a,b) for a in range(n) for b in range(a+1,n) if adj[a]>>b&1]
dist=[n]*n;dist[0]=dist[1]=0
for _ in range(n):
 for a,b in edges:dist[a]=min(dist[a],dist[b]+1);dist[b]=min(dist[b],dist[a]+1)
cycles=[]
for k in range(3,n+1):
 for s in it.combinations(range(n),k):
  for tail in it.permutations(s[1:]):
   cyc=(s[0],)+tail
   if cyc[1]>cyc[-1]:continue
   if all(adj[cyc[j]]>>cyc[(j+1)%k]&1 for j in range(k)):cycles.append(cyc)
 if cycles:break
sets=[[i for i in range(n) if s>>i&1] for s in x['mis']]
o=dict(edges=edges,degrees=[a.bit_count() for a in adj],distances_from_edge=dist,girth=len(cycles[0]),shortest_cycles=cycles,maximum_independent_sets=sets,e=x['e'],positive_separator=['1/1000','7/27','1/3'],separator_value='67027/67500',canonical_trees=len(x['trees']),source_conditions='d=3, r=2; root endpoints degree 3, other vertices degree <=3, all vertices distance <=2, girth6')
assert dist==x['graph']['layers'] and len(cycles[0])==6
(D/'outputs/edge-graph-check.json').write_text(json.dumps(o,indent=2)+'\n');print(o)
