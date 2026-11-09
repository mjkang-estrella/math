import sys,pathlib,itertools,json,time,random
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r99/deps'))
import networkx as nx,numpy as np
from scipy.optimize import linprog
mul=lambda a,b:((a[0]*b[0]+2*a[1]*b[1])%5,(a[0]*b[1]+a[1]*b[0])%5)
F=list(itertools.product(range(5),repeat=2));squares={mul(a,a) for a in F if a!=(0,0)}
g=nx.Graph();g.add_nodes_from(range(25));g.add_edges_from((i,j) for i in range(25) for j in range(i+1,25) if ((F[i][0]-F[j][0])%5,(F[i][1]-F[j][1])%5) in squares)
seen=set();out=[];count=0;valid=0
for size in [4,6,8]:
 for X in itertools.combinations(range(25),size):
  count+=1;S=set(X);T=set(range(25))-S;degrees=[len(set(g[x])&S) for x in X]
  if len(set(degrees))!=1:continue
  half=[v for v in T if len(set(g[v])&S)==size//2]
  if not half or any(len(set(g[v])&S) not in [0,size//2,size] for v in T):continue
  h=g.copy()
  for v in half:
   for x in X:
    if h.has_edge(v,x):h.remove_edge(v,x)
    else:h.add_edge(v,x)
  if len(set(dict(h.degree()).values()))!=1:continue
  valid+=1;alpha=max(map(len,nx.find_cliques(nx.complement(h))))
  sig=(alpha,tuple(sorted(nx.triangles(h).values())))
  # test every alpha<5 instance; sample first few alpha5 for validation
  if alpha==5 and len(out)>=3:continue
  A=nx.to_numpy_array(h);M=A+3*np.eye(25);statuses=[]
  for v in range(25):
   keep=[j for j in range(25) if j not in h[v]]
   spec=abs(np.linalg.eigvalsh(A[np.ix_(keep,keep)])[0]+3)<1e-7
   r=linprog(np.zeros(25),A_eq=M,b_eq=np.ones(25)*3,bounds=[(0,0) if j in h[v] else (0,None) for j in range(25)],method='highs',options={'threads':2})
   statuses.append(spec and r.success)
   if not statuses[-1]:break
  rec={'X':X,'alpha':alpha,'adverse_numeric':all(statuses),'vertices_checked':len(statuses),'graph6':nx.to_graph6_bytes(h,header=False).decode().strip()};out.append(rec);print(rec,flush=True)
  if alpha<5 and all(statuses):break
 else:
  print('size complete',size,'tested',count,'valid',valid,flush=True);continue
 break
(D/'outputs/adverse-switch.json').write_text(json.dumps({'tested':count,'valid':valid,'candidates':out},indent=2)+'\n')
