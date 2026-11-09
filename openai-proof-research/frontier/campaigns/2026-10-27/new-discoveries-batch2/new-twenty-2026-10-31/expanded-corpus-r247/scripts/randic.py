import os,resource,time,json,pathlib
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1';os.environ['MALLOC_ARENA_MAX']='2'
import networkx as nx
import numpy as np
L=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic()
def en(g):
 a=nx.to_numpy_array(g); d=a.sum(axis=1); a/=np.sqrt(d[:,None]*d[None,:]);return float(np.abs(np.linalg.eigvalsh(a)).sum())
def sun(n):
 g=nx.Graph();g.add_nodes_from(range(n))
 if n%2:
  for i in range((n-1)//2):g.add_edges_from([(0,1+2*i),(1+2*i,2+2*i)])
 else:
  g.add_edge(0,1);s=(n-2)//2;p=(s+1)//2
  for i in range(s):g.add_edges_from([(0 if i<p else 1,2+2*i),(2+2*i,3+2*i)])
 return g
out=[]
for n in range(3,19):
 bound=en(sun(n));best=-1;count=0;edges=None
 for g in nx.nonisomorphic_trees(n):
  v=en(g);count+=1
  if v>best:best=v;edges=list(g.edges())
  if time.monotonic()-start>105:break
 r={'n':n,'tested':count,'complete':time.monotonic()-start<=105,'largest_numeric_energy':best,'sun_bound':bound,'difference':best-bound,'maximizer_edges':edges};out.append(r);print(json.dumps(r),flush=True)
 if best>bound+1e-8 or time.monotonic()-start>105:break
(L/'randic-results.json').write_text(json.dumps({'method':'nonisomorphic trees, double-precision diagnostic only','networkx':nx.__version__,'numpy':np.__version__,'elapsed':time.monotonic()-start,'rows':out},indent=2))
