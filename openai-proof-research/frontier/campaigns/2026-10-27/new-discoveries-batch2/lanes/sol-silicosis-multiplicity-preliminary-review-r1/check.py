from fractions import Fraction as Q
from itertools import product,combinations
from pathlib import Path
import json,random,hashlib,datetime
O=Path(__file__).resolve().parent
def mul(p,q):
 r=[Q(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]+=a*b
 return r
def var(v):
 v=[1 if x>0 else -1 for x in v if x];return sum(a!=b for a,b in zip(v,v[1:]))
def basis(d):
 n=len(d);cols=[]
 for i in range(n+1):
  p=[Q(1)]
  for t in d[i:]:p=mul(p,[t,1])
  cols.append([Q(0)]*i+p)
 return [[cols[j][i] for j in range(n+1)] for i in range(n+1)]
def det(A):
 A=[r[:] for r in A];ans=Q(1)
 for k in range(len(A)):
  z=next((i for i in range(k,len(A)) if A[i][k]),None)
  if z is None:return Q(0)
  if z!=k:A[z],A[k]=A[k],A[z];ans=-ans
  t=A[k][k];ans*=t
  for i in range(k+1,len(A)):
   q=A[i][k]/t
   for j in range(k+1,len(A)):A[i][j]-=q*A[k][j]
 return ans
count=minors=identities=0
ds=[[Q(2),Q(1,3),Q(7),Q(1,11),Q(5)], [Q(1,7),Q(9),Q(1,2),Q(9),Q(1,3)]]
for d in ds:
 A=basis(d);n=len(d)
 for c in product([-2,-1,0,1,2],repeat=n+1):
  y=[sum(a*b for a,b in zip(row,c)) for row in A]
  assert var(y)<=var(c);count+=1
 for k in range(1,n+2):
  for rows in combinations(range(n+1),k):
   for cols in combinations(range(n+1),k):
    assert det([[A[i][j] for j in cols] for i in rows])>=0;minors+=1
 for x in [Q(1,13),Q(1),Q(23,2)]:
  p=Q(1);tel=Q(0);H=Q(0);G=-Q(3,5)*Q(7,3)
  for i,di in enumerate(d,1):
   p*=x/(x+di);tel+=di*p;H+=i*i*p;G+=(i*i-Q(3,5)*di)*p
  assert tel==x*(1-p)
  assert G==H-Q(3,5)*(x+Q(7,3))+Q(3,5)*x*p
  assert G!=H-Q(3,5)*(x+Q(7,3));identities+=3
# Evaluate the finite coefficient matrix via an independent Horner evaluation.
rng=random.Random(190110670)
for z in range(300):
 d=[Q(rng.randrange(1,20),rng.randrange(1,20)) for _ in range(rng.randrange(1,10))];A=basis(d)
 c=[Q(rng.randrange(-5,6)) for _ in range(len(d)+1)];x=Q(rng.randrange(1,20),rng.randrange(1,20))
 y=[sum(a*b for a,b in zip(row,c)) for row in A];v=Q(0)
 for a in reversed(y):v=v*x+a
 p=Q(1);g=c[0];D=Q(1)
 for i,di in enumerate(d,1):p*=x/(x+di);g+=c[i]*p;D*=x+di
 assert v==D*g;assert var(y)<=var(c);identities+=1
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exhaustive_sign_vectors=count,nonnegative_minors=minors,exact_identities=identities,status='PASS',scope='finite diagnostics only; analytic proof independently reviewed in review.md')
(O/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
