import os
os.environ['OMP_NUM_THREADS']='1';os.environ['OPENBLAS_NUM_THREADS']='1'
from pathlib import Path
import numpy as np,json,math,itertools,time
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
p=Path(__file__).parent
out=[]
for mods,rs in [([4,4],[5,6,7]),([8,4],[9,10,11,13]),([9,3],[10,11])]:
 pts=list(itertools.product(*(range(m) for m in mods)));N=len(pts);e=math.lcm(*mods);idx={x:i for i,x in enumerate(pts)}
 M=lil_matrix((N*N+1,2*N));lb=np.full(N*N+1,-np.inf);ub=np.ones(N*N+1)
 row=0
 for i,a in enumerate(pts):
  for j,b in enumerate(pts):
   M[row,i]+=1;M[row,j]+=1;M[row,N+idx[tuple((a[k]-b[k])%mods[k] for k in range(len(mods)))]]=-1;row+=1
 M[row,:N]=1;M=M.tocsr();c=np.r_[np.zeros(N),np.ones(N)];lo=np.zeros(2*N);hi=np.ones(2*N);lo[0]=1
 for r in rs:
  ds={a*b for a in range(1,N//e+1) if N//e%a==0 and a*e>=r for b in range(1,e+1) if e%b==0};target=min(d*(2*((r+d-1)//d)-1) for d in ds)
  lb[row]=ub[row]=r;t=time.time();res=milp(c,integrality=np.ones(2*N),bounds=Bounds(lo,hi),constraints=LinearConstraint(M,lb,ub),options={'time_limit':4,'mip_rel_gap':0})
  witness=[pts[i] for i in range(N) if res.x is not None and res.x[i]>.5];D={tuple((a[k]-b[k])%mods[k] for k in range(len(mods))) for a in witness for b in witness}
  v=dict(mods=mods,r=r,target=target,status=int(res.status),message=res.message,witness=witness,exact_witness_size=len(witness),exact_difference_size=len(D),lower_bound=float(res.mip_dual_bound) if res.x is not None else None,seconds=time.time()-t)
  out.append(v);(p/'difference-milp-diagnostics.json').write_text(json.dumps(out,indent=2));print(mods,r,target,len(D),res.status,flush=True)
