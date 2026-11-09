import sys,pathlib,itertools,json,time
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r99/deps'))
import networkx as nx,numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
n=int(sys.argv[1]);seed=int(sys.argv[2]);g=nx.complete_graph(4) if n==4 else nx.random_regular_graph(3,n,seed=seed)
arcs=list(g.to_directed().edges());aidx={a:j for j,a in enumerate(arcs)};na=len(arcs);V=n*n*na
idx=lambda k,r,i,a:(k*n+r)*na+aidx[i,a]
I=[];J=[];val=[];rhs=[]
def eq(items,b=0):
 row=len(rhs)
 for j,v in items:I.append(row);J.append(j);val.append(v)
 rhs.append(b)
for k in range(n):
 for r in range(1,n):
  for i in range(n):eq([(idx(k,r,i,a),1) for a in g[i]]+[(idx(k,r-1,a,i),-1) for a in g[i]])
 for r in range(1,n):
  for i in range(n):eq([(idx(k,r,i,a),1) for a in g[i]]+[(idx(i,n-r,k,a),-1) for a in g[k]])
 for i,a in arcs:
  if k: eq([(idx(k,r,i,a),1) for r in range(n)]+[(idx(0,r,i,a),-1) for r in range(n)])
 for i in range(n):eq([(idx(k,r,i,a),1) for r in range(n) for a in g[i]],1)
for r in range(n):
 for i,a in arcs:
  if r:eq([(idx(k,r,i,a),1) for k in range(n)]+[(idx(k,0,i,a),-1) for k in range(n)])
 for i in range(n):eq([(idx(k,r,i,a),1) for k in range(n) for a in g[i]],1)
M=coo_matrix((val,(I,J)),shape=(len(rhs),V)).tocsr();bounds=[(0,0) if r==0 and i!=k else (0,None) for k in range(n) for r in range(n) for i,a in arcs]
print('model',n,seed,V,len(rhs),flush=True)
for mode in ['edge','cut']:
 sets=list(g.edges())[:3] if mode=='edge' else [set(range(n//2)),set(range(3)),set(range(n//2+1))]
 for S in sets:
  c=np.zeros(V)
  aa=[S,tuple(reversed(S))] if mode=='edge' else [(i,a) for i,a in arcs if i in S and a not in S]+[(a,i) for i,a in arcs if i in S and a not in S]
  for i,a in aa:
   for r in range(n):c[idx(0,r,i,a)]=-1 if mode=='edge' else 1
  res=linprog(c,A_eq=M,b_eq=rhs,bounds=bounds,method='highs',options={'time_limit':30,'threads':2})
  print(mode,list(S),res.status,res.fun,res.message,flush=True)
  if res.success and ((mode=='edge' and res.fun < -1.00001) or (mode=='cut' and res.fun<1.99999)):
   from fractions import Fraction
   x=[str(Fraction(float(z)).limit_denominator(1000000)) for z in res.x]
   (D/f'outputs/dfj-{n}-{seed}-{mode}.json').write_text(json.dumps({'n':n,'seed':seed,'edges':list(g.edges()),'arcs':arcs,'objective':res.fun,'mode':mode,'set':list(S),'x':x})+'\n')
