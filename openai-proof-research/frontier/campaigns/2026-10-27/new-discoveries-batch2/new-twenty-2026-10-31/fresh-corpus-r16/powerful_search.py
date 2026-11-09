import os,resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
os.sched_setaffinity(0,{0,1})
os.environ['OMP_NUM_THREADS']='2';os.environ['OPENBLAS_NUM_THREADS']='2'
import numpy as np, scipy.optimize as so, scipy.sparse as sp, json,time,resource
from pathlib import Path
p=Path(__file__).resolve().parent
for n in [7,8]:
 N=1<<n; rows=[];lo=[];hi=[];nv=N
 def row(d,l,h):rows.append(d);lo.append(l);hi.append(h)
 row({x:1 for x in range(N)},N//2,N//2);row({0:1},1,1)
 for mask in range(1,N):
  k=n-mask.bit_count(); zs=list(range(nv,nv+k+1));nv+=k+1
  row(dict.fromkeys(zs,1),1,1)
  d={x:1 for x in range(N) if not x&mask};d.update({z:-(1<<j) for j,z in enumerate(zs)});row(d,0,0)
 for j in range(n):
  ys=[]
  for x in range(N):
   if not x&(1<<j):
    y=nv;nv+=1;ys.append(y);row({y:1,x:-1},-np.inf,0);row({y:1,x+(1<<j):-1},-np.inf,0)
  row(dict.fromkeys(ys,1),1,np.inf)
 rr=[];cc=[];dd=[]
 for i,d in enumerate(rows):
  for j,v in d.items():rr.append(i);cc.append(j);dd.append(v)
 A=sp.coo_matrix((np.array(dd,float),(rr,cc)),shape=(len(rows),nv)).tocsc();t=time.monotonic()
 r=so.milp(np.zeros(nv),integrality=np.ones(nv),bounds=so.Bounds(0,1),constraints=so.LinearConstraint(A,lo,hi),options={'time_limit':90,'threads':2})
 out={'n':n,'variables':nv,'constraints':len(rows),'status':int(r.status),'message':r.message,'elapsed':time.monotonic()-t,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'proof':False}
 if r.x is not None:
  S=[x for x in range(N) if r.x[x]>.5];counts=[sum(not x&m for x in S) for m in range(N)];out['S']=S;out['exact_check']=len(S)==N//2 and all(c>0 and c&(c-1)==0 for c in counts) and all(any(x in S and x^(1<<j) in S for x in range(N)) for j in range(n))
 (p/f'powerful-n{n}.json').write_text(json.dumps(out,indent=2));print(json.dumps(out),flush=True)
