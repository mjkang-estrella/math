from itertools import product,combinations
from fractions import Fraction as F
from pathlib import Path
import json
L=Path(__file__).resolve().parent;controls=0;replacement=0;graphs=0
for a in range(1,5):
 edges=list(combinations(range(a),2));zs={}
 for t,d in [(1,3),(1,2),(2,3)]:
  u=F(t,d+t);q=1-F(t,d)**2;rho=F(d-t,d)
  for mask in range(1<<len(edges)):
   es=[e for i,e in enumerate(edges) if mask>>i&1];e=len(es);W=0;occ=[0]*a;opp={v:0 for v in edges}
   for state in product(range(3),repeat=a): # 0=T,1=N,2=S
    cross=sum({state[x],state[y]}=={0,2} for x,y in es)
    w=t**sum(s!=1 for s in state)*(d-t)**sum(s==1 for s in state)*(d-t)**cross*d**(e-cross)
    W+=w
    for x in range(a):
     if state[x]==2:occ[x]+=w
    for x,y in edges:
     if state[x]==2 and state[y]==0:opp[x,y]+=w
   Z=F(W,(d+t)**a*d**e);zs[t,d,mask]=Z
   for x in range(a):assert F(occ[x],W)<=u;controls+=1
   for v in edges:assert F(opp[v],W)<=u*u;controls+=1
   graphs+=1
  for mask in range(1<<len(edges)):
   active=[i for i in range(len(edges)) if mask>>i&1]
   for k in [1,2]:
    for rem in combinations(active,k):
     m0=mask
     for i in rem:m0^=1<<i
     assert zs[t,d,mask]>=q*zs[t,d,m0];replacement+=1
out=dict(status='PASS; diagnostic only',weighted_core_models=graphs,marginal_and_opposite_controls=controls,one_two_edge_replacement_controls=replacement,max_core_vertices=4,probabilities=['1/3','1/2','2/3'])
(L/'correlation-checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
