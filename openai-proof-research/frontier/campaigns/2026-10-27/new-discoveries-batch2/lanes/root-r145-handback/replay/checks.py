import json,random,time,hashlib
from pathlib import Path
from fractions import Fraction as F
import tinygraph as nx
L=Path(__file__).resolve().parent
def inertia(A):
 A=[[F(x) for x in row] for row in A];p=z=n=0
 while A:
  k=next((i for i in range(len(A)) if A[i][i]),None)
  if k is not None:
   a=A[k][k];p+=a>0;n+=a<0
   inds=[i for i in range(len(A)) if i!=k]
   A=[[A[i][j]-A[i][k]*A[k][j]/a for j in inds] for i in inds]
  else:
   pair=next(((i,j) for i in range(len(A)) for j in range(i) if A[i][j]),None)
   if pair is None:z+=len(A);break
   u,v=pair;b=A[u][v];p+=1;n+=1
   inds=[i for i in range(len(A)) if i not in pair]
   A=[[A[i][j]-(A[i][u]*A[v][j]+A[i][v]*A[u][j])/b for j in inds] for i in inds]
 return [p,z,n]
def mat(G):
 v=list(G);return [[G.degree(x)-2 if x==y else int(G.has_edge(x,y)) for y in v] for x in v]
def sig(G):
 p,z,n=inertia(mat(G));c=G.number_of_edges()-len(G)+1
 return p-n+1-c
def witness(G):return dict(n=len(G),m=G.number_of_edges(),edges=sorted(map(sorted,G.edges())),signature=sig(G),c=G.number_of_edges()-len(G)+1)
def leaf(G,x):
 H=G.copy();H.add_edge(x,max(H)+1);return H
def cycles(a,b,d):
 G=nx.cycle_graph(a);H=nx.relabel_nodes(nx.cycle_graph(b),lambda x:x+a)
 G=nx.compose(G,H);prev=0
 for j in range(d-1):v=a+b+j;G.add_edge(prev,v);prev=v
 G.add_edge(prev,a);return G
R=random.Random(1452026);start=time.monotonic();out=dict(seed=1452026,arithmetic='exact Fraction symmetric congruence',scope='bounded samples, no proof',failures=[],controls=[],samples=0,by_c={},synergy=None,independent_checks=0)
# Published c=2 monotonicity counterexample and c=4 control.
G=cycles(4,5,2);out['controls'].append([witness(G),witness(leaf(G,9))]);assert sig(G)==0 and sig(leaf(G,9))==1
G=nx.complete_bipartite_graph(3,3);G.remove_edge(0,3);nx.add_path(G,[0,6,7,8,3]);out['controls'].append([witness(G),witness(leaf(G,6))]);assert sig(G)==0 and sig(leaf(G,6))==1
digest=hashlib.sha256()
for t in range(2000):
 n=R.randrange(8,27);c=R.randrange(2,8)
 G=nx.from_prufer_sequence([R.randrange(n) for _ in range(n-2)])
 missing=list(nx.non_edges(G));R.shuffle(missing);G.add_edges_from(missing[:c])
 # Add up to eight vertices as a general rooted forest, not just a star.
 for j in range(R.randrange(9)):
  G.add_edge(R.randrange(len(G)),len(G))
 s=sig(G);out['samples']+=1;out['by_c'][c]=out['by_c'].get(c,0)+1
 digest.update(json.dumps([sorted(map(sorted,G.edges())),s]).encode())
 if 2*s>c+1:out['failures'].append(witness(G))
 if t<24:
  H=nx.line_graph(G);v=list(H);A=[[int(H.has_edge(x,y)) for y in v] for x in v]
  p,z,q=inertia(A);assert p-q==s;out['independent_checks']+=1
 if t<180:
  H=nx.convert_node_labels_to_integers(nx.k_core(G,2));base=sig(H)
  if len(H)>1:
   x,y=R.sample(list(H),2);sx=sig(leaf(H,x));sy=sig(leaf(H,y));J=leaf(leaf(H,x),y);sxy=sig(J)
   if sx<=base and sy<=base and sxy>base and out['synergy'] is None:
    out['synergy']=dict(core=witness(H),x=x,y=y,single_signatures=[sx,sy],joint=witness(J))
out['sample_digest']=digest.hexdigest();out['seconds']=time.monotonic()-start
(L/'check-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
