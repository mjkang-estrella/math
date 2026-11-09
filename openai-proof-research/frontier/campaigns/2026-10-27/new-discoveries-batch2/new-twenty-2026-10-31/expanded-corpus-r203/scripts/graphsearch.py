import sys,pathlib; sys.dont_write_bytecode=True; sys.path.insert(0,str(pathlib.Path(sys.argv[0]).resolve().parents[1]/"deps"))
import networkx as nx,itertools,json,sys
mode=sys.argv[1];rows=[]
for G in nx.graph_atlas_g():
 n=len(G)
 if n<3:continue
 if mode=='factors':
  if min(dict(G.degree()).values())<2:continue
  inds=[S for k in range(1,n+1) for S in itertools.combinations(G,k) if all(not G.has_edge(a,b) for a,b in itertools.combinations(S,2))]
  if any(len(S)>min(G.degree(v) for v in S)-1 for S in inds):continue
  cycles=[]
  for k in range(3,n+1):
   for S in itertools.combinations(G,k):
    for p in itertools.permutations(S[1:]):
     c=(S[0],)+p
     if c[1]>c[-1]:continue
     if all(G.has_edge(c[j],c[(j+1)%k]) for j in range(k)):cycles.append(sum(1<<v for v in c));break
  def cover(mask):
   if not mask:return 0
   v=mask&-mask;return min([1+cover(mask^c) for c in cycles if c&v and c&mask==c] or [n+1])
  best=cover((1<<n)-1)
  ks=[k for k in range(1,n+1) if min([sum(G.degree(v) for v in S) for S in inds if len(S)==k+1] or [10**9])>=n]
  assert best<=min(ks),(list(G.edges()),best,ks)
  rows.append({'n':n,'edges':list(G.edges()),'minimum_cycles':best,'minimum_hypothesis_k':min(ks)})
 elif mode=='fs' and n<=5 and nx.is_connected(G):
  P=list(itertools.permutations(range(n)));F=nx.Graph();F.add_nodes_from(P)
  for p in P:
   pos=p.index(0)
   for j in G[pos]:q=list(p);q[pos],q[j]=q[j],q[pos];F.add_edge(p,tuple(q))
  if not nx.is_connected(F):continue
  # All pairs, no orbit reduction assumption.
  count=0
  for j,p in enumerate(P):
   for q in P[j+1:]:
    k=nx.algorithms.connectivity.local_node_connectivity(F,p,q);assert k==min(F.degree(p),F.degree(q)),(G.edges(),p,q,k)
    count+=1
  rows.append({'n':n,'edges':list(G.edges()),'pairs':count})
print(json.dumps({'mode':mode,'graphs_checked':len(rows),'rows':rows},indent=2))
