import networkx as nx,itertools,random
import networkx as nx,itertools,json,random
from fractions import Fraction
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def mu(g):
 v=list(g);total=count=0
 for k in range(1,len(v)+1):
  for sub in itertools.combinations(v,k):
   h=g.subgraph(sub)
   if not nx.is_connected(h):continue
   if k==1:t=1
   else:
    import sympy as sp
    mat=nx.laplacian_matrix(h).toarray();t=int(sp.Matrix(mat[:-1,:-1]).det())
   count+=t;total+=k*t
 return Fraction(total,count)
def gamma(g,d):
 v=list(g);ds=dict(nx.all_pairs_shortest_path_length(g));balls={x:{y for y in v if ds[x][y]<=d} for x in v}
 for k in range(1,len(v)+1):
  for sub in itertools.combinations(v,k):
   if any(g.has_edge(x,y) for x,y in itertools.combinations(sub,2)):continue
   if len(set().union(*(balls[x] for x in sub)))==len(v):return k

rng=random.Random(6503)
for m in [3,4,5]:
 core=nx.path_graph(m);g=core.copy()
 for v in range(m):g.add_edges_from([(v,m+2*v),(m+2*v,m+2*v+1)])
 part=nx.bipartite.color(g);extras=[(u,v) for u,v in itertools.combinations(g,2) if part[u]!=part[v] and not g.has_edge(u,v)]
 cases=hits=0
 for size in [1,2,3]:
  combos=list(itertools.combinations(extras,size));rng.shuffle(combos)
  for es in combos[:200]:
   h=g.copy();h.add_edges_from(es);z=gamma(h,2);cases+=1
   if z==m:
    hits+=1
    # Necessary corona test: each leaf is end of pendant path length 2 and paths partition V.
    blocks=[]
    for v in h:
     if h.degree(v)==1:
      w=next(iter(h[v]))
      if h.degree(w)==2:blocks.append({v,w,next(x for x in h[w] if x!=v)})
    corona=len(blocks)==m and len(set.union(*blocks))==3*m
    if not corona:print('CANDIDATE',m,es,list(h.edges()),flush=True);raise SystemExit
 print('corona_mutations',m,'tested',cases,'equalities',hits,'all_corona',True,flush=True)
