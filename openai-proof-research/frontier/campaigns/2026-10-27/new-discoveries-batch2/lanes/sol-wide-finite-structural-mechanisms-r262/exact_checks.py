from explore import *
import itertools,numpy as np
def ts(n):return [(x,y,x+y//2) for x in range(1,n+1) for y in range(1,n+1) if x+y//2<=n]
def direct(b):return sum(b[x]==b[y]==b[z] for x,y,z in ts(len(b)-1))
def parity(b):
 n=len(b)-1;r=0
 for v in range(n//2+1):
  ys=[y for y in [2*v,2*v+1] if 1<=y<=n]
  for x in range(1,n-v+1):
   if b[x]==b[x+v]:r+=sum(b[x]==b[y] for y in ys)
 return r
checks=0
for n in range(1,9):
 for c in itertools.product([0,1],repeat=n):
  b=(0,)+c;assert direct(b)==parity(b);checks+=1
 assert len(ts(n))==n*n-(n*n//4)
edgechecks=0
for n in range(2,41):
 w=[[0]*n for _ in range(n)]
 for t in ts(n):
  for a,b in itertools.combinations(t,2):
   if a!=b:w[a-1][b-1]+=1;w[b-1][a-1]+=1
 for i in range(1,n+1):
  for j in range(i+1,n+1):
   exact=int(i+j//2<=n)+int(j+i//2<=n)+int(2*(j-i)<=n)+int(2*(j-i)+1<=n)+1+int(i-j//2>=1)
   assert exact==w[i-1][j-1];edgechecks+=1
 R=2*n+(2*n+1)//3;assert sum(map(sum,w))//2==3*len(ts(n))-R
 if n==12:
  W=np.array(w,dtype=np.int64);c=np.array([1 if i<2 or 6<=i<10 else -1 for i in range(n)],dtype=np.int64)
  Q=W-np.diag(c*(W@c));ev,V=np.linalg.eigh(Q);v=np.rint(1000*V[:,0]).astype(np.int64);value=int(v@Q@v);assert value<0
  witness=dict(n=12,v=[int(x) for x in v],integer_quadratic_value=value)
result=dict(exhaustive_parity_identity_colorings=checks,analytic_weight_entry_checks=edgechecks,n_range=[2,40],spectral_failure_exact=witness,status='PASS identities and failed-certificate witness only; NOT source conjecture')
(L/'exact-checks.json').write_text(json.dumps(result,indent=2));print(result)
