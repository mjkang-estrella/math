from pathlib import Path
import sys,itertools
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3,networkx as nx
counts={}
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2 or n>6 or min(dict(G.degree()).values())==0:continue
 dim=(2*n+2)//3;s=z3.Solver();s.set(timeout=600);xs=[[z3.Real(f'x{i}_{k}') for k in range(dim)] for i in range(n)];r=[z3.Real('r'+str(i)) for i in range(n)];ds={}
 for i in range(n):s.add(r[i]>0)
 s.add(r[0]==1)
 for i,j in itertools.combinations(range(n),2):
  d=z3.Real(f'd{i}_{j}');ds[i,j]=d;diff=[xs[i][k]-xs[j][k] for k in range(dim)];s.add(*[d>=v for v in diff],*[d>=-v for v in diff],z3.Or(*[d==v for v in diff],*[d==-v for v in diff]),d>=r[i],d>=r[j]);s.add(d<r[i]+r[j] if G.has_edge(i,j) else d>=r[i]+r[j])
 for i in range(n):s.add(z3.Or([ds[min(i,j),max(i,j)]==r[i] for j in range(n) if j!=i]))
 ans=str(s.check());key=str((n,ans));counts[key]=counts.get(key,0)+1
 if ans=='unsat':print('WITNESS',nx.to_graph6_bytes(G,header=False).decode(),dim,flush=True)
print('COMPLETE',counts,flush=True)
