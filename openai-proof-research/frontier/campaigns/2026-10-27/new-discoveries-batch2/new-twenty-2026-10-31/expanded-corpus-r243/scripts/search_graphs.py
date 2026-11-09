import networkx as nx,random,json,time,sys
rng=random.Random(243);start=time.monotonic()
def chordless(g):
 for u,v in list(g.edges()):
  g.remove_edge(u,v)
  bad=any(u in c and v in c for c in nx.biconnected_components(g))
  g.add_edge(u,v)
  if bad:return False
 return True
def alpha(g):
 vs=[v for v in g if g.degree(v)<=2];idx={v:i for i,v in enumerate(vs)};adj=[sum(1<<idx[w] for w in g[v] if w in idx) for v in vs]
 def rec(mask):
  if not mask:return 0
  i=(mask&-mask).bit_length()-1
  return max(rec(mask&~(1<<i)),1+rec(mask&~((1<<i)|adj[i])))
 return rec((1<<len(vs))-1),len(vs)
count=0;worst=None
for g in nx.graph_atlas_g():
 if not len(g) or not nx.is_connected(g) or not chordless(g):continue
 a,l=alpha(g);count+=1
 if 6*a<len(g):print('COUNTEREXAMPLE',nx.to_graph6_bytes(g).decode());sys.exit(2)
print(json.dumps({'atlas_connected_chordless':count,'orders':'1..7','counterexamples':0}),flush=True)
for n in [8,10,12,16,20,24,30]:
 done=0;best=1
 for rep in range(80):
  g=nx.random_labeled_tree(n,seed=rng) if hasattr(nx,'random_labeled_tree') else nx.random_tree(n,seed=rng)
  pairs=list(nx.non_edges(g));rng.shuffle(pairs)
  for u,v in pairs:
   g.add_edge(u,v)
   if not chordless(g):g.remove_edge(u,v)
  a,l=alpha(g);done+=1;best=min(best,a/n)
  if 6*a<n:print(json.dumps({'COUNTEREXAMPLE':nx.to_graph6_bytes(g).decode(),'n':n,'alpha':a}),flush=True);sys.exit(2)
 print(json.dumps({'n':n,'samples':done,'best_alpha_ratio':best,'counterexamples':0,'elapsed':time.monotonic()-start}),flush=True)
