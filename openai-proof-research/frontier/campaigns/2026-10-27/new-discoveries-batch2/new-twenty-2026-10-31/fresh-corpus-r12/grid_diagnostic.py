import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import numpy as np,json,time,itertools
from pathlib import Path
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
p=Path(__file__).parent
results=[]
for n,k in [(5,3),(6,3),(7,3),(8,3),(9,3),(10,3),(15,3),(20,3),(4,8),(4,10),(6,12),(8,16)]:
 pts=list(itertools.product(range(n),range(k)));trip=set()
 for a,(x,y) in enumerate(pts):
  ds={}
  for b,(u,v) in enumerate(pts):
   if a!=b:ds.setdefault((x-u)**2+(y-v)**2,[]).append(b)
  for group in ds.values():
   for b,c in itertools.combinations(group,2):
    u,v=pts[b];s,t=pts[c]
    if (u-x)*(t-y)!=(s-x)*(v-y):trip.add(tuple(sorted((a,b,c))))
 ri=[];ci=[]
 for i,t in enumerate(trip):
  ri.extend([i]*3);ci.extend(t)
 A=coo_matrix((np.ones(len(ci)),(ri,ci)),shape=(len(trip),len(pts))).tocsc()
 start=time.monotonic();res=milp(-np.ones(len(pts)),integrality=np.ones(len(pts)),bounds=Bounds(0,1),constraints=LinearConstraint(A,-np.inf,2),options={'time_limit':20,'threads':2})
 sel=[pts[i] for i,v in enumerate(res.x) if v>0.5] if res.x is not None else []
 valid=all(not set(t)<=set(i for i,v in enumerate(res.x) if v>0.5) for t in trip) if res.x is not None else False
 row={'n':n,'k':k,'forbidden_triples':len(trip),'status':res.message,'size':len(sel),'selected':sel,'valid_exact_integer_check':valid,'seconds':time.monotonic()-start,'mip_gap':getattr(res,'mip_gap',None)}
 results.append(row);print(row,flush=True);(p/'grid-diagnostics.json').write_text(json.dumps(results,indent=2)+'\n')
