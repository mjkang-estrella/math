import sys,pathlib;sys.path.insert(0,str(pathlib.Path(__file__).resolve().parents[1]/"vendor"))
import networkx as nx,itertools,json,pathlib
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1]; out=[]
for G in nx.graph_atlas_g():
 n=len(G)
 if not n:continue
 E=list(G.edges());N=[list(G[v]) for v in range(n)]
 chi=0; good=None
 for k in range(1,n+1):
  if any(all(a[u]!=a[v] for u,v in E) for a in itertools.product(range(k),repeat=n)):
   chi=k;break
 for a in itertools.product(range(1,chi+1),repeat=n):
  s=[sum(a[w] for w in N[v]) for v in range(n)]
  if all(s[u]!=s[v] for u,v in E):good=a;break
 if good is None: print('ADDITIVE FAILURE',nx.to_graph6_bytes(G,header=False),flush=True)
 # count each undirected cycle once by smallest vertex, smaller second than last
 counts=[0]*(n+1)
 for root in G:
  def dfs(path):
   u=path[-1]
   for v in G[u]:
    if v==root and len(path)>=3:
     if path[1]<path[-1]:counts[len(path)]+=1
    elif v>root and v not in path:dfs(path+[v])
  dfs([root])
 A=[[Fraction(int(G.has_edge(u,v))) for v in G] for u in G];sig=0
 while A:
  nA=len(A);p=next((i for i in range(nA) if A[i][i]),None)
  if p is not None:
   a=A[p][p];sig+=1 if a>0 else -1;inds=[i for i in range(nA) if i!=p];A=[[A[i][j]-A[i][p]*A[p][j]/a for j in inds] for i in inds]
  else:
   pair=next(((i,j) for i in range(nA) for j in range(i+1,nA) if A[i][j]),None)
   if pair is None:break
   p,q=pair;a=A[p][q];inds=[i for i in range(nA) if i not in pair];A=[[A[i][j]-(A[i][p]*A[q][j]+A[i][q]*A[p][j])/a for j in inds] for i in inds]
 c3=sum(counts[3::4]);c5=sum(counts[5::4]);assert -c3<=sig<=c5
 upc=n>=3 and all(counts[j]==1 for j in range(3,n+1))
 out.append({'g6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'m':len(E),'chi':chi,'additive_witness':good,'signature_float_diagnostic':sig,'cycle_counts':counts,'UPC':upc})
print('atlas graphs',len(out),'UPC',[(r['n'],r['m'],r['g6']) for r in out if r['UPC']],flush=True)
(D/'outputs/atlas.json').write_text(json.dumps(out)+'\n')
