from pathlib import Path
import json,time
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
L=Path(__file__).resolve().parent
def comp(n,d):
 if n==1:return [(d,)]
 return [(a,)+b for a in range(d+1) for b in comp(n-1,d-a)]
r=[];start=time.monotonic()
for n,d in [(3,d) for d in range(3,9)]+[(4,d) for d in range(3,6)]+[(5,3)]:
 if time.monotonic()-start>95:break
 vs=comp(n,d);N=len(vs);edges=[(i,j) for i in range(N) for j in range(i) if sum(abs(a-b) for a,b in zip(vs[i],vs[j]))==2]
 C=np.eye(N)
 for i,j in edges:C[i,j]=C[j,i]=1
 opts={'time_limit':5,'mip_rel_gap':0,'threads':1};c=np.ones(N);base=LinearConstraint(C,np.ones(N),np.full(N,np.inf))
 a=milp(c,integrality=c,bounds=Bounds(0,1),constraints=base,options=opts)
 E=np.zeros((len(edges),N))
 for k,(i,j) in enumerate(edges):E[k,i]=E[k,j]=1
 b=milp(c,integrality=c,bounds=Bounds(0,1),constraints=[base,LinearConstraint(E,np.full(len(edges),-np.inf),np.ones(len(edges)))],options=opts)
 row={'n':n,'d':d,'vertices':N,'gamma_status':a.status,'independent_status':b.status,'gamma':a.fun,'independent':b.fun,'gamma_bound':getattr(a,'mip_dual_bound',None),'independent_bound':getattr(b,'mip_dual_bound',None)}
 for label,z in [('dominating',a),('independent',b)]:
  if z.x is not None:
   x=np.rint(z.x);assert np.all(C@x>=1)
   if label=='independent':assert np.all(E@x<=1)
   row[label+'_witness']=[vs[i] for i in range(N) if x[i]]
 r.append(row);print({k:v for k,v in row.items() if not k.endswith('witness')},flush=True)
(L/'monomial-diagnostics.json').write_text(json.dumps(r,indent=2))
