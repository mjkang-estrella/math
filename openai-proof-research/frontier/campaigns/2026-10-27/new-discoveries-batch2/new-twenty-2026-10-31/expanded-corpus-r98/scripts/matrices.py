import itertools, math, numpy as np,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];res=[]
def rank(A,p):
 A=A.copy()%p;r=0
 for c in range(A.shape[1]):
  hits=np.flatnonzero(A[r:,c]);
  if not len(hits):continue
  t=r+int(hits[0]);A[[r,t]]=A[[t,r]];A[r]=A[r]*pow(int(A[r,c]),-1,p)%p
  A[r+1:]=(A[r+1:]-A[r+1:,c,None]*A[r])%p;r+=1
  if r==A.shape[0]:break
 return r
for n in range(2,17):
 for j in range(min(4,(n+1)//3)+1):
  cols=[sum(1<<(x-1) for x in a) for a in itertools.combinations(range(1,n+1),j) if all(x>=2*t for t,x in enumerate(a,1))]
  rows=[sum(1<<(x-1) for x in a) for s in range(j+1) for a in itertools.combinations(range(1,n+1),s) if all(2*t<=x<n-2*s+2*t for t,x in enumerate(a,1))]
  A=np.array([[int(r&c==r) for c in cols] for r in rows],dtype=np.int64);rs={p:rank(A,p) for p in [2,3,5,101]};v=dict(n=n,k=j,shape=A.shape,ranks=rs);res.append(v);print(v,flush=True)
  if min(rs.values())<min(A.shape):print('RANK FAILURE',flush=True)
(D/'outputs/matrices.json').write_text(json.dumps(res,indent=2)+'\n')
