import sys,itertools as it,time,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'vendor'))
import networkx as nx
for n in [3,4,5,6]:
 start=time.monotonic();rows=[sum(1<<i for i in c) for c in it.combinations(range(n),3)];matrices=0;planar=0;threeconn=0;bad=[]
 # Row sorting is lossless up to permutation within a bipartition.
 for rs in it.combinations_with_replacement(rows,n):
  if any(sum(r>>j&1 for r in rs)!=3 for j in range(n)):continue
  matrices+=1;G=nx.Graph();G.add_nodes_from(range(2*n));G.add_edges_from((i,n+j) for i,r in enumerate(rs) for j in range(n) if r>>j&1)
  if not nx.is_connected(G):continue
  if not nx.check_planarity(G)[0]:continue
  planar+=1
  if nx.node_connectivity(G)<3:continue
  threeconn+=1
  adj=[list(G[v]) for v in range(2*n)]
  def ham(v,used):
   if used==(1<<(2*n))-1:return 0 in adj[v]
   return any(ham(w,used|1<<w) for w in adj[v] if not used>>w&1)
  if not ham(0,1):bad.append(rs)
 print(json.dumps(dict(bipartition_size=n,row_sorted_regular_matrices=matrices,connected_planar=planar,threeconnected_planar=threeconn,nonhamiltonian=bad,seconds=time.monotonic()-start,scope='Equivalent cubic bipartite graph formulation; legal-system construction not certified')),flush=True)
