import sys,pathlib,json,time,random,itertools
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];sys.dont_write_bytecode=True;sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import networkx as nx
def inertia(A):
 pos=neg=zero=0
 while A:
  n=len(A);p=next((i for i in range(n) if A[i][i]),None)
  if p is not None:
   inds=[j for j in range(n) if j!=p];d=A[p][p];pos+=d>0;neg+=d<0
   A=[[A[i][j]-A[i][p]*A[p][j]/d for j in inds] for i in inds]
  else:
   pair=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i][j]),None)
   if pair is None:zero+=n;break
   i,j=pair;b=A[i][j];inds=[t for t in range(n) if t not in pair];pos+=1;neg+=1
   A=[[A[u][v]-(A[u][i]*A[j][v]+A[u][j]*A[i][v])/b for v in inds] for u in inds]
 return pos,neg,zero
out={'graphs':0,'tested_with_padding':0,'by_order':{},'counterexamples':[],'method':'Exact rational congruence inertia of nL-2mI; zeros included in sigma; atlas to7 and seeded random8..18, padding0..4'};start=time.monotonic();r=random.Random(337250)
def gen():
 yield from (g for g in nx.graph_atlas_g() if len(g))
 for n in range(8,19):
  for j in range(80):yield nx.gnp_random_graph(n,r.choice([.1,.2,.35,.5,.7,.9]),seed=r)
for g in gen():
 if time.monotonic()-start>100:break
 n=len(g);m=g.number_of_edges();out['graphs']+=1;out['by_order'][str(n)]=out['by_order'].get(str(n),0)+1
 for s in range(5):
  N=n+s;L=[[F((N*g.degree(i)-2*m) if i==j else -N*int(g.has_edge(i,j))) for j in range(n)] for i in range(n)]
  p,neg,z=inertia(L);sigma=p+z+(s if m==0 else 0);out['tested_with_padding']+=1
  deg=sorted(d for _,d in g.degree() if d);rstar=max(deg,default=0);iso=sum(d==0 for _,d in g.degree())+s
  expected=(N==1) or (deg==[1,1]) or (rstar>=2 and deg==[1]*rstar+[rstar] and iso<rstar-1)
  if (sigma==1)!=expected:out['counterexamples'].append({'n':n,'edges':list(g.edges()),'padding':s,'sigma':sigma})
 if out['counterexamples']:break
 (D/'outputs/spectral.json').write_text(json.dumps(out,indent=2))
out['wall_seconds']=time.monotonic()-start;(D/'outputs/spectral.json').write_text(json.dumps(out,indent=2));print(out)
