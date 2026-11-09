"""Exact bounded diagnostic; run through the specified helper_guard, never as proof."""
import itertools,json,pathlib,random,collections
L=pathlib.Path(__file__).resolve().parent
def conflict(a,b):
 es=sorted(a|b); adj=[set() for _ in es]
 for i,e in enumerate(es):
  for j,f in enumerate(es[:i]):
   if set(e)&set(f) and ((e in a and f in a) or (e in b and f in b)):adj[i].add(j);adj[j].add(i)
 return es,adj
def color(adj,k):
 c=[-1]*len(adj);nodes=0
 def go():
  nonlocal nodes
  nodes+=1
  if nodes>200000:raise RuntimeError('fixed search-node cap')
  todo=[i for i in range(len(adj)) if c[i]<0]
  if not todo:return True
  i=max(todo,key=lambda j:(len({c[v] for v in adj[j] if c[v]>=0}),len(adj[j])))
  used={c[v] for v in adj[i]}
  for x in range(k):
   if x not in used:
    c[i]=x
    if go():return True
  c[i]=-1;return False
 return go(),nodes
def degree(es):return max(collections.Counter(v for e in es for v in e).values(),default=0)
out={}
# A proper shared precoloring can block all Delta+2 colors at one new edge.
h={(0,j) for j in [2,3,4]}|{(1,j) for j in [5,6,7]};a=h|{(0,1)};b=h
es,adj=conflict(a,b);i=es.index((0,1));fixed={es.index(e):j for j,e in enumerate(sorted(h))}
assert degree(a)==4 and degree(b)==3 and len({fixed[v] for v in adj[i]})==6
assert all(fixed[u]!=fixed[v] for u in fixed for v in adj[u] if v in fixed)
assert color(adj,6)[0]
out['blocked_precolor']={'G1':sorted(a),'G2':sorted(b),'shared_colors':[(es[u],v) for u,v in fixed.items()],'conclusion':'arbitrary fixed shared precoloring need not extend; recoloring permitted restores feasibility'}
# Conflict graphs need not be line graphs: an induced claw.
a={(0,1),(0,2),(1,3)};b={(0,1),(0,4)};es,adj=conflict(a,b)
i=es.index((0,1));leaves=set(range(4))-{i}
assert adj[i]==leaves and all(not(adj[j]&leaves) for j in leaves)
out['induced_claw']={'G1':sorted(a),'G2':sorted(b),'conflict_edges':[(es[u],es[v]) for u in range(4) for v in adj[u] if u<v]}
# Full exact census on four labeled vertices, every ordered pair of simple graphs.
edges=list(itertools.combinations(range(4),2));graphs=[{e for j,e in enumerate(edges) if mask>>j&1} for mask in range(64)]
count=peak=0
for a in graphs:
 for b in graphs:
  es,adj=conflict(a,b);d=max(degree(a),degree(b));ok,nodes=color(adj,d+2)
  assert ok;count+=1;peak=max(peak,nodes)
out['four_vertex_census']={'ordered_pairs':count,'peak_nodes':peak,'result':'all Delta+2 colorable; diagnostic only'}
(L/'exact-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
