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
rng=random.Random(6501);res=[]
# all atlas bipartite connected graphs with admissible divisibility, then random 9,12 vertices
for g in nx.graph_atlas_g():
 n=len(g)
 if n<3 or not nx.is_connected(g) or not nx.is_bipartite(g):continue
 for d in range(2,4):
  if n%(d+1):continue
  z=gamma(g,d)
  if z*(d+1)==n:res.append({'n':n,'d':d,'edges':list(g.edges()),'gamma':z})
print('atlas_equalities',res,flush=True)
for n in [9,12]:
 hits=[]
 for trial in range(600):
  a=rng.randrange(2,n-1);g=nx.bipartite.random_graph(a,n-a,rng.uniform(.15,.6),seed=rng)
  if not nx.is_connected(g):continue
  z=gamma(g,2)
  if z*3==n:hits.append({'edges':list(g.edges()),'degrees':sorted(dict(g.degree()).values())})
 print('random_equalities',n,hits,flush=True)
# full connected graph atlas through 6 vertices, every edge contraction (simple graph)
best=(Fraction(100),None)
for g in nx.graph_atlas_g():
 n=len(g)
 if n<2 or n>6 or not nx.is_connected(g):continue
 x=mu(g)
 for e in g.edges():
  h=nx.contracted_edge(g,e,self_loops=False);diff=x-mu(h)
  if diff<best[0]:best=(diff,{'edges':list(g.edges()),'edge':e,'mu':str(x),'contracted_mu':str(mu(h))})
  if diff<Fraction(1,3):print('COUNTEREXAMPLE',best,flush=True);raise SystemExit
print('contraction_best',best,flush=True)
