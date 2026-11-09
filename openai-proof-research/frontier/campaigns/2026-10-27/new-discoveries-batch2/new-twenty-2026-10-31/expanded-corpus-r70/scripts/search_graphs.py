import networkx as nx,itertools,json,pathlib,fractions,collections
D=pathlib.Path(__file__).resolve().parents[1];out={};counts=collections.Counter();bad=[]
def matchings(G):
 es=list(G.edges());ans=[]
 def go(j,used,chosen):
  if j==len(es):ans.append(chosen);return
  go(j+1,used,chosen)
  u,v=es[j]
  if u not in used and v not in used:go(j+1,used|{u,v},chosen+[es[j]])
 go(0,set(),[]);return ans
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2 or not nx.is_connected(G):continue
 counts['connected_atlas']+=1;es=list(G.edges());deg=dict(G.degree());delta=min(deg.values());Delta=max(deg.values());M=matchings(G)
 if Delta<=4:
  counts['375345']+=1
  sat=min(len(A) for A in M if all(any(x in set(sum((list(e) for e in A),[])) for x in e) for e in es))
  H=sum((fractions.Fraction(2,deg[u]+deg[v]) for u,v in es),fractions.Fraction())
  if sat>H:bad.append(dict(id=375345,edges=es,sat=sat,H=str(H)))
 d=nx.diameter(G)
 if d>=3 and n==2*d+1:
  counts['374919']+=1;w=sum(sum(v.values()) for _,v in nx.all_pairs_shortest_path_length(G))/2
  if w>n*d*(d+1)/2:bad.append(dict(id=374919,edges=es,W=w))
 # Every source-eligible k; test matching deletions.
 conn=nx.node_connectivity(G)
 for k in range(1,conn+1):
  if delta<k+2:continue
  counts['374905']+=1;size=min(n//2,delta)
  good=False
  for A in M:
   if len(A)!=size:continue
   H=G.copy();H.remove_edges_from(A)
   if nx.node_connectivity(H)>=k:good=True;break
  if not good:bad.append(dict(id=374905,k=k,edges=es))
 # edge-removable all non-isomorphic trees with delta >= k + m - 1, both connectivities
 for k in range(1,conn+1):
  for m in range(2,delta-k+2):
   for T in nx.nonisomorphic_trees(m):
    counts['374903']+=1;ok=False
    for verts in itertools.permutations(G.nodes(),m):
     A=[(verts[u],verts[v]) for u,v in T.edges()]
     if not all(G.has_edge(*e) for e in A):continue
     H=G.copy();H.remove_edges_from(A)
     if nx.node_connectivity(H)>=k:ok=True;break
    if not ok:bad.append(dict(id=374903,k=k,m=m,edges=es))
 for k in range(1,n):
  # atlas graph is a spanning subgraph of the labelled cycle power; sufficient enumerate all labellings
  if delta<k+1:continue
  if any(all(min(abs(p[u]-p[v]),n-abs(p[u]-p[v]))<=k for u,v in es) for p in itertools.permutations(range(n))):
   counts['375130']+=1
   def ham(path):
    if len(path)==n:return G.has_edge(path[-1],path[0])
    return any(ham(path+[v]) for v in G[path[-1]] if v not in path)
   if not ham([0]):bad.append(dict(id=375130,k=k,edges=es))
print(dict(counts),bad,flush=True)
out={'counts':dict(counts),'counterexamples':bad,'scope':'Connected graph atlas order 2..7, source minimum-degree conditions; Hasunuma vertex-connectivity branch only; Hamilton all vertex labellings. No random coverage.'}
(D/'outputs/graphs.json').write_text(json.dumps(out,indent=2)+'\n')
# Full nonisomorphic trees grouped by order and diameter; every maximizer tested.
r=[]
for n in range(2,15):
 groups={};num=0
 for T in nx.nonisomorphic_trees(n):
  num+=1;dist=dict(nx.all_pairs_shortest_path_length(T));ecc={v:max(dist[v].values()) for v in T};dia=max(ecc.values());W=sum(sum(d.values()) for d in dist.values())//2
  cen={v for v in T if ecc[v]==min(ecc.values())};sums={v:sum(dist[v].values()) for v in T};med={v for v in T if sums[v]==min(sums.values())};good=bool(cen&med)
  if dia not in groups or W>groups[dia]['W']:groups[dia]={'W':W,'bad':[],'maximizers':0}
  if W==groups[dia]['W']:
   groups[dia]['maximizers']+=1
   if not good:groups[dia]['bad'].append(list(T.edges()))
 r.append(dict(n=n,trees=num,diameters=groups));print('trees',n,num,[(d,g) for d,g in groups.items() if g['bad']],flush=True)
 (D/'outputs/trees.json').write_text(json.dumps(r,indent=2)+'\n')
