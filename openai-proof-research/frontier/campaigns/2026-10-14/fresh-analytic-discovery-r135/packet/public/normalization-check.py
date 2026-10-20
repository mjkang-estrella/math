"""Small exact algebra diagnostics, not a mathematical gate. No file writes."""
from fractions import Fraction as F
import json

def tr(a):return list(map(list,zip(*a)))
def mul(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def inv(a):
 n=len(a);b=[[F(v) for v in r]+[F(i==j) for j in range(n)] for i,r in enumerate(a)]
 for i in range(n):
  k=next(k for k in range(i,n) if b[k][i]);b[i],b[k]=b[k],b[i];z=b[i][i];b[i]=[v/z for v in b[i]]
  for k in range(n):
   if k!=i:
    z=b[k][i];b[k]=[v-z*w for v,w in zip(b[k],b[i])]
 return [r[n:] for r in b]
def det(a):
 a=[[F(x) for x in r] for r in a];v=F(1)
 for i in range(len(a)):
  k=next((k for k in range(i,len(a)) if a[k][i]),None)
  if k is None:return F(0)
  if k!=i:a[i],a[k]=a[k],a[i];v=-v
  z=a[i][i];v*=z
  for k in range(i+1,len(a)):
   q=a[k][i]/z
   a[k]=[x-q*y for x,y in zip(a[k],a[i])]
 return v
rows=[]
for d in (1,2,3):
 n=2*d;B=[[F(((i+2)*(j+3))%7-3,5) for j in range(n)] for i in range(n)];A=mul(B,tr(B))
 for i in range(n):A[i][i]+=1
 R=[[-A[i][j]/2 for j in range(d)]+[-A[d+i][d+j]/2 for j in range(d)] for i in range(d)]
 G=mul(mul(R,inv(A)),tr(R));beta=1+sum(G[i][i] for i in range(d))
 S=[[beta*F(i==j) for j in range(d)]+R[i] for i in range(d)]
 S += [tr(R)[i]+A[i] for i in range(n)]
 L=[[F(0) for _ in range(3*d)] for _ in range(3*d)]
 D=[[F(0) for _ in range(3*d)] for _ in range(2*d)]
 for i in range(d):
  L[i][i]=L[d+i][i]=L[2*d+i][i]=L[d+i][d+i]=L[2*d+i][2*d+i]=1
  D[i][i]=D[d+i][i]=-1;D[i][d+i]=D[d+i][2*d+i]=1
 C=mul(mul(L,S),tr(L))
 assert all(C[k*d+i][k*d+j]==beta*F(i==j) for k in range(3) for i in range(d) for j in range(d))
 assert mul(mul(D,C),tr(D))==A
 assert all(det([r[:j] for r in C[:j]])>0 for j in range(1,3*d+1))
 rows.append({'d':d,'beta':str(beta),'diagonal_blocks':'exact','normal_covariance':'exact','positive_principal_minors':3*d})
assert (F(1,12)/F(1,108))==9
print(json.dumps({'covariance_examples':rows,'branch_reference_ratio':'9','limits':'finite rational diagnostics only; no theorem, SDE, entropy or contribution verification'},indent=2))
