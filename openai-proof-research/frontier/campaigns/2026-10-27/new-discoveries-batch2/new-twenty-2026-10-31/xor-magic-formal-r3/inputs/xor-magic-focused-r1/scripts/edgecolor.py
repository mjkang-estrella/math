import json,sys,itertools
from pathlib import Path
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
p=Path(sys.argv[1]);g=json.loads(p.read_text());N=g['N'];E=list(map(tuple,g['edges']));comp=int(sys.argv[2]);
if comp:E=sorted(set(itertools.combinations(range(N),2))-set(E))
d=2*len(E)//N;m=len(E);A=lil_matrix((m+N*d,m*d));rhs=np.ones(m+N*d)
for j,(u,v) in enumerate(E):
 for c in range(d):A[j,j*d+c]=1;A[m+u*d+c,j*d+c]=1;A[m+v*d+c,j*d+c]=1
r=milp(np.zeros(m*d),integrality=np.ones(m*d),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),rhs,rhs),options={'time_limit':25,'disp':True})
out=dict(input=str(p),complement=bool(comp),status=int(r.status),message=r.message)
if r.x is not None:
 F=[[E[j] for j in range(m) if r.x[j*d+c]>.5] for c in range(d)];assert all(len(f)==N//2 and len({u for e in f for u in e})==N for f in F);assert set(e for f in F for e in f)==set(E);out['factors']=F
Path('outputs/'+p.stem+f'-factors-{comp}.json').write_text(json.dumps(out,indent=2));print(out['status'],bool(r.x is not None))
