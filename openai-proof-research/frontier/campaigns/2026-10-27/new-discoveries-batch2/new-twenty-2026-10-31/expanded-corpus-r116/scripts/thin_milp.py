import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import csc_matrix
from itertools import product
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];out=[]
for p,m in [(3,3),(3,4),(3,5),(3,6),(5,3),(5,4),(7,3)]:
 V=np.array([v for v in product(range(p),repeat=m) if 0<sum(v)<=m*p],dtype=np.int16);U=np.array(list(product(range(p),repeat=m))[1:],dtype=np.int16)
 dot=(U@V.T)%p;zero=dot==0;non=dot!=0
 A=csc_matrix(np.vstack([V.T,zero,non]).astype(float));lb=np.r_[np.full(m,p),np.ones(2*len(U))];ub=np.r_[np.full(m,p),np.full(2*len(U),np.inf)]
 r=milp(np.ones(len(V)),integrality=np.ones(len(V)),bounds=Bounds(0,p),constraints=LinearConstraint(A,lb,ub),options={'time_limit':12,'threads':2})
 q={'p':p,'m':m,'columns':len(V),'status':int(r.status),'message':r.message,'bound':float(r.mip_gap) if getattr(r,'mip_gap',None) is not None else None}
 if r.x is not None:
  x=np.rint(r.x).astype(int);q['candidate_columns']=[v.tolist() for v,k in zip(V,x) for _ in range(k)];q['checked']=bool(np.all(V.T@x==p) and np.all(zero@x>=1) and np.all(non@x>=1))
 print(q,flush=True);out.append(q);(D/'outputs/thin-milp.json').write_text(json.dumps(out,indent=2)+'\n')
