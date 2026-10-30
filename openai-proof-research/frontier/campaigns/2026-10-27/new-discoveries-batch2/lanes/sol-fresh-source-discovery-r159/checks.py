from itertools import combinations
from fractions import Fraction as Q
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def counts(n,edges):
 E={tuple(sorted(e)) for e in edges}; out=[0]*n
 for S in combinations(range(n),3):
  if sum(e in E for e in combinations(S,2))==2:
   for v in S:out[v]+=1
 return out
tot=0; irregular=[]; identity=0
for n in range(3,6):
 pairs=list(combinations(range(n),2))
 for mask in range(1<<len(pairs)):
  E={e for i,e in enumerate(pairs) if mask>>i&1}; c=counts(n,E); tot+=1
  if len(set(c))==n:irregular.append([n,mask])
  N=[{j for j in range(n) if tuple(sorted((i,j))) in E} for i in range(n)]
  for v in range(n):
   ordinary=len(N[v])*(len(N[v])-1)//2+sum(len(N[u])-1 for u in N[v])
   triangles=sum(tuple(sorted((a,b))) in E for a,b in combinations(N[v],2))
   assert c[v]==ordinary-3*triangles;identity+=1
assert not irregular
n=4; expectations=[Q(0)]*n
for S in combinations(range(n),3):
 es=list(combinations(S,2)); ps=[Q((a+1)*(b+1),100) for a,b in es]
 prob=sum((1-ps[k])*ps[(k+1)%3]*ps[(k+2)%3] for k in range(3))
 for v in S:expectations[v]+=prob
assert len(set(expectations))==4
# Every graph has positive probability in this product distribution; none is irregular.
assert all(0<Q((a+1)*(b+1),100)<1 for a,b in combinations(range(4),2))
parts=[[0],[1,2],[3,4,5]]; E={(a,b) for i,j in [(0,1),(1,2)] for a in parts[i] for b in parts[j]}; c=counts(6,E)
assert c[1]==c[2] and c[3]==c[4]==c[5]
out=dict(graphs=tot,vertex_identity_checks=identity,no_irregular_orders=[3,4,5],distinct_expectations=[str(x) for x in expectations],expectation_method_falsified=True,blowup_counts=c,scope='Exact finite route controls, not proof or counterexample to Conjecture 3')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
