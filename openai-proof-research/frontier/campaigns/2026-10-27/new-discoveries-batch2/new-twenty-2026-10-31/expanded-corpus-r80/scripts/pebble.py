import sys,pathlib,json,itertools,functools
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'outputs/python-packages'));import networkx as nx
def comps(k,n):
 if n==1:yield (k,);return
 for j in range(k+1):
  for c in comps(k-j,n-1):yield (j,)+c
rows=[]
for gi,G in enumerate(nx.graph_atlas_g()):
 n=len(G)
 if not 1<=n<=4 or not nx.is_connected(G):continue
 edges=[(u,v) for u,v in G.edges()]+[(v,u) for u,v in G.edges()]
 def number(target):
  @functools.lru_cache(None)
  def can(c):
   if all(c[i]>=target[i] for i in range(n)):return True
   for u,v in edges:
    if c[u]>=2:
     a=list(c);a[u]-=2;a[v]+=1
     if can(tuple(a)):return True
   return False
  for size in range(1,65):
   if all(can(c) for c in comps(size,n)):return size
  raise RuntimeError('upper cap')
 for t in range(1,4):
  concentrated=[number(tuple(t if i==r else 0 for i in range(n))) for r in range(n)];pt=max(concentrated)
  for target in comps(t,n):
   p=number(target);bound=pt-sum(v>0 for v in target)+1
   row=dict(graph_atlas=gi,n=n,edges=list(G.edges()),t=t,target=target,pebbling=p,pi_t=pt,bound=bound,pass_bound=p<=bound);rows.append(row)
  (D/'outputs/pebble.json').write_text(json.dumps(rows,indent=2));print(gi,t,len(rows),flush=True)
assert all(r['pass_bound'] for r in rows)
