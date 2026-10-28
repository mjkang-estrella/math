import json
from pathlib import Path

def coeffs(n,N):
 B=[0]*(n+2);B[0]=1
 B[1]-=1;B[n]+=1;B[n+1]-=1
 for j in range(1,n+1):B[j]-=1
 f=[1]
 for i in range(1,N):
  f.append(-sum(B[j]*f[i-j] for j in range(1,min(i,n+1)+1))-sum(f[j]*f[i-1-j] for j in range(i)))
 return f

def det(A):
 A=[r[:] for r in A];n=len(A)
 if not n:return 1
 prev=1;sign=1
 for k in range(n-1):
  if A[k][k]==0:
   t=next((r for r in range(k+1,n) if A[r][k]),None)
   if t is None:return 0
   A[k],A[t]=A[t],A[k];sign=-sign
  z=A[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    num=z*A[i][j]-A[i][k]*A[k][j];assert num%prev==0;A[i][j]=num//prev
  for i in range(k+1,n):A[i][k]=0
  prev=z
 return sign*A[-1][-1]

checks=0;singular=[]
for n in [1,2,3]:
 f=coeffs(n,45)
 D=lambda shift,j:det([[f[shift+a+b] for b in range(j)] for a in range(j)])
 for shift in range(8):
  for j in range(1,9):
   assert D(shift,j+1)*D(shift+2,j-1)==D(shift,j)*D(shift+2,j)-D(shift+1,j)**2;checks+=1
 s=n+1
 for k in range(12):
  A1=D(s,k+1);A2=D(s,k+2);b=D(s+1,k+1);X=D(s+2,k)
  if A1==0 and A2!=0:
   assert A2*X==-b*b
   singular.append(dict(n=n,k=k,A2=A2,B=b,X=X,positive_sign_claim_valid=A2*X==b*b))
f=coeffs(1,45);D=lambda shift,j:det([[f[shift+a+b] for b in range(j)] for a in range(j)])
fit=[]
for m in range(3):
 val=D(5,8*m);guess=(2*m+1)*(4*m+1);assert val==guess;fit.append(dict(m=m,value=val))
result=dict(t_system_checks=checks,singular_cases=singular,residue_diagnostics=fit,scope="finite exact diagnostics only, no all-index result")
Path(__file__).with_name("independent-checks.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result))
