import os
for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,time,json,pathlib,math
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
p=pathlib.Path(__file__).resolve().parent
# Katona's one-sided formula is used diagnostically, not as a certified theorem.
def m(n,t):
 if (n+t)%2==0:return sum(math.comb(n,j) for j in range((n+t)//2,n+1))
 return 2*sum(math.comb(n-1,j) for j in range((n+t-1)//2,n))
def solve(types,weights,compatible,limit):
 rr=[];cc=[];bb=[]
 for i,a in enumerate(types):
  for j in range(i):
   if not compatible(a,types[j]):
    rr.extend([len(bb)]*2);cc.extend([i,j]);bb.append(1)
 A=coo_matrix((np.ones(len(rr)),(rr,cc)),shape=(len(bb),len(types))).tocsc()
 z=milp(-np.array(weights,dtype=float),integrality=np.ones(len(types)),bounds=Bounds(0,1),constraints=LinearConstraint(A,-np.inf,bb),options={'time_limit':limit,'threads':1})
 return {'status':int(z.status),'message':z.message,'incumbent':None if z.x is None else int(round(-z.fun)),'dual_upper':None if getattr(z,'mip_dual_bound',None) is None else -float(z.mip_dual_bound),'selected':None if z.x is None else [a for a,x in zip(types,z.x) if x>.5]}
out=[];start=time.time()
for n,t,s in [(6,2,2),(7,2,2),(8,2,2),(8,2,3),(8,3,3),(9,3,3)]:
 types=[a for a in range(1<<n) if t<=a.bit_count()<=n-s];ok=lambda a,b:(a&b).bit_count()>=t and (a|b).bit_count()<=n-s
 z=solve(types,[1]*len(types),ok,6);z.update(mode='unrestricted',n=n,t=t,s=s,product=max(m(k,t)*m(n-k,s) for k in range(t,n-s+1)));out.append(z);print(json.dumps(z),flush=True)
# Second mechanism: exact combinatorial orbit compatibility under S_u x S_v.
# Pairwise minimum intersections/max unions attained independently in both blocks.
for n,t,s in [(12,2,2),(12,3,3),(14,3,3),(14,4,4),(16,3,4),(18,4,4),(20,5,5)]:
 for u in [n//2,n//2-2]:
  v=n-u;ok=lambda x,y:max(0,x[0]+y[0]-u)+max(0,x[1]+y[1]-v)>=t and min(u,x[0]+y[0])+min(v,x[1]+y[1])<=n-s
  types=[(a,b) for a in range(u+1) for b in range(v+1) if ok((a,b),(a,b))];w=[math.comb(u,a)*math.comb(v,b) for a,b in types]
  z=solve(types,w,ok,2);z.update(mode='two-block-orbits',n=n,t=t,s=s,u=u,product=max(m(k,t)*m(n-k,s) for k in range(t,n-s+1)));out.append(z);print(json.dumps(z),flush=True)
(p/'product-diagnostic.json').write_text(json.dumps({'elapsed':time.time()-start,'warning':'Floating MILP diagnostic; no proof or exhaustive certification','runs':out},indent=2)+'\n')
