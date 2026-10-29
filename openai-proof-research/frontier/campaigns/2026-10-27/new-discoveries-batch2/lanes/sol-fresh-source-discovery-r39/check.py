import os,resource,signal,json,pathlib,math
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']: os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2); resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(55)
from fractions import Fraction as F
b=pathlib.Path(__file__).parent
# exact Routh first column for descending coefficients; positive = strict Hurwitz.
def routh(p):
 a=list(map(F,p[::-1])); L=(len(a)+1)//2
 u=a[::2]+[F(0)]*(L-len(a[::2])); v=a[1::2]+[F(0)]*(L-len(a[1::2])); col=[u[0]]
 while len(col)<len(a):
  col.append(v[0])
  if v[0]<=0: return col
  w=[(v[0]*u[j+1]-u[0]*v[j+1])/v[0] for j in range(L-1)]+[F(0)]
  u,v=v,w
 return col
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b): c[i+j]+=x*y
 return c
def stepq(q,n):
 # source s_(3,n)/x in terms of s_(3,n-1)/x
 c=[0]*(len(q)+1)
 for j,a in enumerate(q): c[j]+=(j+1)*a;c[j+1]+=math.comb(n+2*j+3,2)*a
 return c
# Direct associated partition DP independent of source triangular recurrence.
N=35; M=3*N
A=[[0]*(N+1) for _ in range(M+1)];A[0][0]=1
for t in range(1,M+1):
 for k in range(1,min(t//3,N)+1): A[t][k]=k*A[t-1][k]+(math.comb(t-1,2)*A[t-3][k-1] if t>=3 else 0)
row=[1]; diagnostics=[]
for n in range(1,N+1):
 row=[(math.comb(n+2*k-1,2)*row[k-1] if k else 0)+(k*row[k] if k<len(row) else 0) for k in range(n+1)]
 assert row==[A[n+2*k][k] for k in range(n+1)]
 if n>=2: assert row[1:]==stepq(prev[1:],n)
 col=routh(row[1:]); assert all(x>0 for x in col)
 diagnostics.append({'n':n,'degree_after_zero_removal':n-1,'strict_routh':True})
 prev=row[:]
# Does the recurrence preserve arbitrary real Hurwitz inputs of matching degree?
obstruction=None; tested=0
for n in range(4,11):
 for a in [1,2,4,8]:
  for den in [1,10,100]:
   for bb in [1,10,100]:
    q=[1]
    for k in range((n-2)//2): q=mul(q,[bb,F(a,den),1])
    while len(q)<n-1:q=mul(q,[1,1])
    assert all(t>0 for t in routh(q));tested+=1
    image=stepq(q,n);c=routh(image)
    if any(t<=0 for t in c):
     obstruction={'n':n,'input':[str(t) for t in q],'image':[str(t) for t in image],'routh_column':[str(t) for t in c]};break
   if obstruction:break
  if obstruction:break
 if obstruction:break
out={'source_checks':diagnostics,'operator_inputs_tested':tested,'operator_obstruction':obstruction,'claim':'finite diagnostics only; no source conjecture proof'}
(b/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
