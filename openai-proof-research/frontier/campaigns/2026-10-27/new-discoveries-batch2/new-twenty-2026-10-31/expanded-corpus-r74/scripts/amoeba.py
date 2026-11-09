import pathlib,json,itertools,os,resource,time,sys
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def global_amoeba(G):
 n=len(G);deg=dict(G.degree());parent=list(range(n))
 def root(x):
  while parent[x]!=x:x=parent[x]
  return x
 def merge(p):
  for i in range(n):parent[root(i)]=root(p[i])
 es={frozenset(e) for e in G.edges()};H=G.copy()
 # Include every neutral automorphism and every isomorphism after one edge replacement.
 for p in nx.isomorphism.GraphMatcher(G,G).isomorphisms_iter():merge(p)
 for e in list(G.edges()):
  H.remove_edge(*e)
  for f in nx.non_edges(G):
   H.add_edge(*f)
   if sorted(dict(H.degree()).values())==sorted(deg.values()):
    for p in nx.isomorphism.GraphMatcher(G,H).isomorphisms_iter():merge(p)
   H.remove_edge(*f)
  H.add_edge(*e)
 leaves={root(i) for i in range(n) if deg[i]==1}
 return all(root(i) in leaves for i in range(n)),[root(i) for i in range(n)]
def check(G,label):
 n=len(G);q=n//2;H=nx.Graph();H.add_nodes_from(range(n));H.add_edges_from(itertools.combinations(range(q,n),2));H.add_edges_from((i,q+j) for i in range(q) for j in range(i+1));ok,orbits=global_amoeba(G);r={'label':label,'n':n,'edges':list(G.edges()),'global':ok,'orbits':orbits,'is_Hn':nx.is_isomorphic(G,H)};out.append(r);print(json.dumps(r),flush=True);(D/'outputs'/f'amoeba-{sys.argv[1]}.json').write_text(json.dumps(out,indent=2))
if sys.argv[1]=='atlas':
 for j,G in enumerate(nx.graph_atlas_g()):
  n=len(G)
  if n>=2 and min(dict(G.degree()).values())==1 and G.number_of_edges()==n*n//4:check(G,f'atlas-{j}')
else:
 n=int(sys.argv[1]);q=n//2;r=n-q;seen=[];total=0
 choices=[list(itertools.combinations(range(q,n),i)) for i in range(1,q+1)]
 for rows in itertools.product(*choices):
  G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(itertools.combinations(range(q,n),2));G.add_edges_from((i,v) for i,row in enumerate(rows) for v in row);total+=1
  if any(nx.is_isomorphic(G,H) for H in seen):continue
  seen.append(G.copy());check(G,f'split-{total}')
 print('labeled_row_patterns',total,'isomorphism_types',len(seen),flush=True)
