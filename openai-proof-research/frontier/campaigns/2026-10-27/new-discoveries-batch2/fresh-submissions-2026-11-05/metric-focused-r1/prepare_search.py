from pathlib import Path
import networkx as nx,json
p=Path(__file__).parent
out=[];counts={}
for n in range(1,14):
 gs=[nx.empty_graph(1)] if n==1 else nx.nonisomorphic_trees(n)
 count=0
 for g in gs:
  roots={}
  def canon(v,parent):return '('+''.join(sorted(canon(w,v) for w in g[v] if w!=parent))+')'
  for r in g:roots.setdefault(canon(r,-1),r)
  out.append(dict(n=n,edges=list(g.edges()),roots=list(roots.values()),tree=True));count+=len(roots)
 counts[str(n)]=count
for g in nx.graph_atlas_g():
 if len(g)>0 and nx.is_connected(g) and not nx.is_tree(g):out.append(dict(n=len(g),edges=list(g.edges()),roots=list(g),tree=False))
(p/'search-input.json').write_text(json.dumps(out))
(p/'search-scope.json').write_text(json.dumps(dict(tree_rooted_counts=counts,graphs=len(out),atlas_non_trees=sum(not g['tree'] for g in out)),indent=2))
print(counts,len(out))
