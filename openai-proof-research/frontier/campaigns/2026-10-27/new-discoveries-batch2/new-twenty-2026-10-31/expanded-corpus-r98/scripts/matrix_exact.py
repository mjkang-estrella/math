import itertools,json,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def det(A):
 n=len(A);last=1;sg=1
 for k in range(n-1):
  p=next((t for t in range(k,n) if A[t][k]),None)
  if p is None:return 0
  if p!=k:A[k],A[p]=A[p],A[k];sg=-sg
  v=A[k][k]
  for i in range(k+1,n):
   z=A[i][k]
   for j in range(k+1,n):
    q=v*A[i][j]-z*A[k][j];assert q%last==0;A[i][j]=q//last
   A[i][k]=0
  last=v
 return sg*A[-1][-1]
out=[]
for n in range(2,int(sys.argv[1])+1):
 for k in range(min(4,(n+1)//3)+1):
  cols=[sum(1<<(x-1) for x in a) for a in itertools.combinations(range(1,n+1),k) if all(x>=2*t for t,x in enumerate(a,1))]
  rows=[sum(1<<(x-1) for x in a) for s in range(k+1) for a in itertools.combinations(range(1,n+1),s) if all(2*t<=x<n-2*s+2*t for t,x in enumerate(a,1))]
  assert len(rows)==len(cols);v=det([[int(r&c==r) for c in cols] for r in rows]);o=dict(n=n,k=k,size=len(rows),det=v);out.append(o);print(json.dumps(o),flush=True)
(D/'outputs/matrix-exact.json').write_text(json.dumps(out,indent=2)+'\n')
