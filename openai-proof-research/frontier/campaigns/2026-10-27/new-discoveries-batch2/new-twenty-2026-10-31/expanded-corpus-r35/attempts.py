import os,resource,pathlib,json,itertools,time
os.environ.update(OMP_NUM_THREADS='2',OPENBLAS_NUM_THREADS='2',MKL_NUM_THREADS='2');os.sched_setaffinity(0,{0,1});resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(150,150))
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
L=pathlib.Path(__file__).resolve().parent;out=[]
for n,s,r in [(5,2,0),(7,3,0),(8,3,0),(9,4,0),(8,3,1)]:
 words=[sum(1<<i for i in c) for c in itertools.combinations(range(n),s)]
 A=np.array([[int((y^c).bit_count()>r+s) for c in words] for y in range(1<<n) if y.bit_count()>r],dtype=float)
 for extra in [False,True]:
  M=A
  if extra:
   T=np.array([[int(not(t&c)) for c in words] for t in range(1<<n) if t.bit_count()==r+3],dtype=float);M=np.vstack([A,T])
  t=time.monotonic();res=milp(np.ones(len(words)),integrality=np.ones(len(words)),bounds=Bounds(0,1),constraints=LinearConstraint(M,1,np.inf),options={'time_limit':12,'threads':2})
  row=dict(n=n,s=s,r=r,forbid_transversal_rplus3=extra,status=int(res.status),message=res.message,elapsed=time.monotonic()-t)
  if res.x is not None:
   code=[c for c,x in zip(words,res.x) if x>.5];tau=min(y.bit_count() for y in range(1<<n) if all(y&c for c in code));row.update(code=code,size=len(code),tau=tau,exact_ball_identity=all((y.bit_count()<=r)==all((y^c).bit_count()<=r+s for c in code) for y in range(1<<n)))
  out.append(row);print(json.dumps(row),flush=True);(L/'ppric-diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
poly=[]
for u,v in [(4,5),(5,4)]:
 M=S.diag(3,3,4,4,u,v)
 for i,j in [(0,4),(1,4),(2,5),(3,5),(4,5)]:M[i,j]=M[j,i]=-1
 D=smith_normal_form(M,domain=S.ZZ);invariants=[abs(int(D[i,i])) for i in range(6)];poly.append(dict(u=u,v=v,matrix=[list(map(int,M.row(i))) for i in range(6)],smith_diagonal=invariants,mu=sum(x>1 for x in invariants),central_chain_trees=u*v-1,warning='Diagnostic cycle-presentation matrices only; exact source path-decomposition and graph/group bridges unproved'))
(L/'polygon-diagnostics.json').write_text(json.dumps(poly,indent=2)+'\n');print(json.dumps(poly),flush=True)
