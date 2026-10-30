import json,itertools,runpy
from pathlib import Path
from fractions import Fraction as F
import tinygraph as nx
L=Path(__file__).resolve().parent
# Load definitions only; do not replay the random experiment on import.
ns={'__file__':str(L/'checks.py')};exec((L/'checks.py').read_text().split('R=random.Random(1452026)')[0],ns)
sig=ns['sig'];inertia=ns['inertia'];mat=ns['mat'];leaf=ns['leaf'];cycles=ns['cycles']
out=dict(c2_core_count=0,c2_core_plus_one_or_two_leaves=0,violations=[],max_signature=-100,scope='residue-representative c2 cores and leaf attachments; not arbitrary forests',synergy={})
def theta(ls):
 G=nx.Graph(2);j=2
 for ell in ls:
  vs=[0]+list(range(j,j+ell-1))+[1];j+=ell-1;nx.add_path(G,vs)
 return G
cores=[]
for ls in itertools.combinations_with_replacement(range(1,6),3):
 if ls.count(1)<=1:cores.append(theta(ls))
for a in range(3,7):
 for b in range(a,7):
  for d in range(1,5):cores.append(cycles(a,b,d))
  G=nx.cycle_graph(a);nx.add_path(G,[0]+list(range(a,a+b-1))+[0]);cores.append(G)
for G in cores:
 out['c2_core_count']+=1
 for x in range(len(G)):
  for y in range(x,len(G)+1):
   H=leaf(G,x)
   if y<len(G):H=leaf(H,y)
   s=sig(H);out['c2_core_plus_one_or_two_leaves']+=1;out['max_signature']=max(out['max_signature'],s)
   if s>1:out['violations'].append(ns['witness'](H))
j=json.loads((L/'check-results.json').read_text())['synergy'];G=nx.Graph(j['core']['n']);G.add_edges_from(j['core']['edges']);A=[[F(v) for v in row] for row in mat(G)];n=len(A);x=j['x'];y=j['y']
# Solve two response columns using a separate exact Gauss-Jordan route.
C=[row+[F(i==x),F(i==y)] for i,row in enumerate(A)]
rank=0;pivots=[]
for k in range(n):
 r=next((i for i in range(rank,n) if C[i][k]),None)
 if r is None:continue
 C[rank],C[r]=C[r],C[rank];a=C[rank][k];C[rank]=[v/a for v in C[rank]]
 for i in range(n):
  if i!=rank:
   a=C[i][k];C[i]=[u-a*v for u,v in zip(C[i],C[rank])]
 pivots.append(k);rank+=1
compatible=[all(C[i][n+j]==0 for i in range(rank,n)) for j in range(2)]
null=[]
for free in set(range(n))-set(pivots):
 v=[F(0)]*n;v[free]=1
 for r,k in enumerate(pivots):v[k]=-C[r][free]
 assert all(sum(A[i][k]*v[k] for k in range(n))==0 for i in range(n))
 null.append([str(a) for a in v])
out['synergy']=dict(rank=rank,null_vectors=null,range_compatible=compatible,response='undefined when incompatible; no pseudoinverse substituted',direct_line_inertias=[])
for H in [G,leaf(G,x),leaf(G,y),leaf(leaf(G,x),y)]:
 J=nx.line_graph(H);out['synergy']['direct_line_inertias'].append(inertia([[int(J.has_edge(a,b)) for b in J] for a in J]))
(L/'structure-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
