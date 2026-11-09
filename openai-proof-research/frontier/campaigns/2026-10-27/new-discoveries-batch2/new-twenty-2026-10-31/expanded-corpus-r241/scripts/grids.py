from pathlib import Path
import sys,itertools
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3,networkx as nx
w,h=map(int,sys.argv[1:]);G=nx.Graph();G.add_nodes_from(itertools.product(range(w),range(h)))
for a,b in list(G):
 for dx,dy in [(1,0),(0,1),(1,1)]:
  if (a+dx,b+dy) in G:G.add_edge((a,b),(a+dx,b+dy))
vs=list(G);es=list(G.edges());T={frozenset(e) for e in nx.minimum_spanning_edges(G,data=False)};free=[i for i,e in enumerate(es) if frozenset(e) not in T];count={}
for mask in range(1<<len(free)):
 signs={i:bool(mask>>j&1) for j,i in enumerate(free)};s=z3.Solver();s.set(timeout=600);xs={v:z3.Int('x'+str(k)) for k,v in enumerate(vs)};sw={v:z3.Bool('s'+str(k)) for k,v in enumerate(vs)};ts={(i,j):z3.Bool(f't{i}_{j}') for i in range(6) for j in range(i+1,6)}
 for v in vs:s.add(xs[v]>=0,xs[v]<6)
 s.add(xs[vs[0]]==0,sw[vs[0]]==False)
 for k,(u,v) in enumerate(es):
  s.add(xs[u]!=xs[v])
  for (i,j),t in ts.items():
   s.add(z3.Implies(z3.Or(z3.And(xs[u]==i,xs[v]==j),z3.And(xs[u]==j,xs[v]==i)),z3.Xor(z3.Xor(t,sw[u]),sw[v])==signs.get(k,False)))
 r=str(s.check());count[r]=count.get(r,0)+1
 if r=='unsat':print('WITNESS',w,h,mask,es,free,flush=True)
 if mask%20==0:print('PROGRESS',mask,count,flush=True)
print('COMPLETE',w,h,len(es),free,count,flush=True)
