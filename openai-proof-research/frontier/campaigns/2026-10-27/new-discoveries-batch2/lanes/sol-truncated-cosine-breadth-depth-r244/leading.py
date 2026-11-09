from fractions import Fraction as F
from itertools import combinations,product
from pathlib import Path
import json
P=Path(__file__).resolve().parent
def weights(u):return [1/F((u[i]-u[(i+1)%3])*(u[i]-u[(i+2)%3])) for i in range(3)]
def diag(u):
 w=weights(u);return sum(w[i]*w[j]*abs(u[i]-u[j])**5/F(20) for i in range(3) for j in range(3))
def cross(u,v):
 w,z=weights(u),weights(v)
 return sum(w[i]*z[j]*max(0,u[i]-v[j])**5/F(20) for i in range(3) for j in range(3))
nodes=list(combinations(range(6),3));count=0;bad=[];minpivot=None;example=None
for U in product(nodes,repeat=3):
 if any(U[j+1][i]<U[j][i] for j in range(2) for i in range(3)):continue
 count+=1;ds=[]
 for j in range(3):
  d=diag(U[j])-(cross(U[j-1],U[j])**2/ds[-1] if j else 0)
  ds.append(d)
  if d<=0:bad.append({'nodes':U,'pivots':list(map(str,ds))});break
 if minpivot is None or min(ds)<minpivot:minpivot=min(ds);example=U
out={'M':3,'triples':len(nodes),'monotone_three_cluster_cases':count,'nonpositive_pivot_cases':bad,'smallest_rational_pivot':str(minpivot),'attaining_nodes':example,'scope':'Exact leading-order effective tridiagonal matrix only; not finite-epsilon or universal certificate.'}
(P/'leading-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
