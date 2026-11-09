"""Bounded exact integer diagnostics; not a Lean certificate. Max one CPU."""
import itertools,json,time,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(110,110))
p=Path(__file__).parent

def stack(a):
 out=[];s=[]
 for x in a:
  while s and s[-1]<x:out.append(s.pop())
  s.append(x)
 return tuple(out+s[::-1])

def sorting():
 rows=[]
 for n in range(2,10):
  cs=[0]*(n+1);ct=[0]*(n+1);identity=tuple(range(n))
  for a in itertools.permutations(range(n)):
   b=a;c=a
   for t in range(n+1):
    cs[t]+=b==identity;ct[t]+=c==identity
    b=stack(b);c=stack(c[::-1])
  rows.append({'n':n,'stack':cs,'revstack':ct,'inequality':all(a<=b for a,b in zip(cs,ct)),'strict_required':all(cs[t]<ct[t] for t in range(3,n-1))})
 (p/'sorting-diagnostic.json').write_text(json.dumps(rows,indent=2))

def partitions(n,lo=1):
 if not n:yield ()
 for x in range(lo,n+1):
  for t in partitions(n-x,x):yield (x,)+t

def ramsey():
 import networkx as nx
 rows=[];atlas=nx.graph_atlas_g()
 for n in range(2,5):
  for m in range(n+1,2*n):
   for parts in partitions(m):
    if max(parts)<2:continue # nonempty means an edge, not just vertices
    F=nx.disjoint_union_all([nx.path_graph(j) for j in parts]);H=nx.Graph(F);H.add_node(m);H.add_edges_from((m,j) for j in range(m))
    r=max(2*n-1,(3*m+1)//2-1,m+n-sum(j%2 for j in parts)-2)
    if r>7:continue
    tested=0;bad=[]
    for G in atlas:
     if len(G)!=r:continue
     if nx.algorithms.isomorphism.GraphMatcher(G,nx.path_graph(n)).subgraph_is_monomorphic():continue
     tested+=1
     if not nx.algorithms.isomorphism.GraphMatcher(nx.complement(G),H).subgraph_is_monomorphic():bad.append(nx.to_graph6_bytes(G,header=False).decode().strip())
    rows.append({'n':n,'forest_components':parts,'conjectured_R':r,'Pn_free_unlabelled_graphs_checked':tested,'counterexamples':bad})
 (p/'ramsey-diagnostic.json').write_text(json.dumps(rows,indent=2))
if __name__=='__main__':
 ramsey();sorting()
