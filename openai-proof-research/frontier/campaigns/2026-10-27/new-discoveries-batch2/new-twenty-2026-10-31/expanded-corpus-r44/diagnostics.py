import os,resource,json,itertools,time
from pathlib import Path
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1';resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import numpy as np
class Graph:
 def __init__(self,edges=()):
  self.adj={}
  for a,b in edges:self.add_edge(a,b)
 def add_edge(self,a,b):self.adj.setdefault(a,set()).add(b);self.adj.setdefault(b,set()).add(a)
 def add_nodes_from(self,vs):
  for v in vs:self.adj.setdefault(v,set())
 def add_edges_from(self,es):
  for e in es:self.add_edge(*e)
 def edges(self):return [(a,b) for a in self.adj for b in self.adj[a] if a<b]
 def __len__(self):return len(self.adj)
 def __getitem__(self,v):return self.adj[v]
 def number_of_edges(self):return len(self.edges())
def diameter(g):
 out=0
 for v in g.adj:
  ds={v:0};q=[v]
  for x in q:
   for y in g[x]:
    if y not in ds:ds[y]=ds[x]+1;q.append(y)
  assert len(ds)==len(g)
  out=max(out,max(ds.values()))
 return out
class nx:
 Graph=Graph
 diameter=diameter
 @staticmethod
 def to_numpy_array(g,nodelist):return np.array([[int(j in g[i]) for j in nodelist] for i in nodelist],dtype=float)
 @staticmethod
 def to_graph6_bytes(g,header=False):return str(g.edges()).encode()
P=Path(__file__).resolve().parent

def graph(k,n,d):
 t=d-(1 if k==3 else 2);a=(t+1)//2;b=t//2;s=n-4-t
 g=nx.Graph([(0,1),(1,2),(2,3),(3,0),(1,3)]);q=4
 for root,l in [(1,a),(3,b)] if k==3 else [(0,a),(2,b)]:
  for _ in range(l):g.add_edge(root,q);root=q;q+=1
 for _ in range(s):g.add_edge(1,q);q+=1
 assert len(g)==n and g.number_of_edges()==n+1 and nx.diameter(g)==d
 return g
rows=[]
for n in range(7,37):
 for d in range(4,n-2):
  gs=[graph(k,n,d) for k in [3,5]];ads=[nx.to_numpy_array(g,nodelist=range(n)) for g in gs]
  for alpha in [.50001,.51,.6,.75,.9,.99]:
   vals=[float(np.linalg.eigvalsh(alpha*np.diag(a.sum(axis=0))+(1-alpha)*a)[-1]) for a in ads];rows.append([n,d,alpha,*vals,vals[0]-vals[1]])
(P/'spectral-diagnostic.json').write_text(json.dumps(rows)+'\n');print('spectral comparisons',len(rows),'minimum gap',min(rows,key=lambda r:r[-1]),'negative gaps',sum(r[-1]<-1e-10 for r in rows),flush=True)
# Exhaustive vertex colorings on the small atlas, and fixed-seed larger bipartite samples.
def crumby(g):
 n=len(g);edges=list(g.edges());paths=set()
 for a,b in edges:
  for x in g[a]:
   for y in g[b]:
    if len({x,a,b,y})==4:paths.add(sum(1<<z for z in [x,a,b,y]))
 adj=[sum(1<<w for w in g[v]) for v in range(n)];allmask=(1<<n)-1
 for red in range(1<<n):
  blue=allmask^red
  if any((red>>v&1 and not(adj[v]&red)) or (blue>>v&1 and (adj[v]&blue).bit_count()>1) for v in range(n)):continue
  if any(red&p==p for p in paths):continue
  return red
 return None
out=[]
# cubic bipartite graphs from unions of three permutation matchings (parallel edges collapse)
rng=np.random.default_rng(4401)
for m in [4,5,6,7,8]:
 for trial in range(30):
  g=nx.Graph();g.add_nodes_from(range(2*m))
  for _ in range(3):g.add_edges_from((i,m+int(j)) for i,j in enumerate(rng.permutation(m)))
  out.append({'edge_list_repr':nx.to_graph6_bytes(g,header=False).decode().strip(),'n':len(g),'coloring':crumby(g)})
(P/'crumby-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n');print('crumby graphs',len(out),'no coloring',[x for x in out if x['coloring'] is None],flush=True)
