from pathlib import Path
import json
D=Path(__file__).resolve().parents[1];P=1000000007;N=600;A=9
M=[[0]*(N+1) for _ in range(A+1)];M[0][0]=1
for s in range(1,N+1):
 for a in range(A,0,-1):
  for k in range(1,N//s+1):
   for n in range(k*s,N+1):M[a][n]=(M[a][n]+k*M[a-1][n-k*s])%P
primes=[n for n in range(2,N+1) if all(n%d for d in range(2,int(n**.5)+1))]
def rank(B):
 B=[x[:] for x in B];r=0
 for j in range(len(B[0])):
  k=next((k for k in range(r,len(B)) if B[k][j]),None)
  if k is None:continue
  B[r],B[k]=B[k],B[r];f=pow(B[r][j],P-2,P);B[r]=[(x*f)%P for x in B[r]]
  for k in range(r+1,len(B)):
   if B[k][j]:
    f=B[k][j];B[k]=[(x-f*y)%P for x,y in zip(B[k],B[r])]
  r+=1
  if r==len(B):break
 return r
out=[]
for a in [2,3,4,5,6,7,8,9]:
 for d in [2,4,6,8]:
  B=[[M[i][n]*pow(n,j,P)%P for i in range(1,a+1) for j in range(d+1)] for n in primes];r=rank(B);row={'a':a,'degree':d,'prime_rows':len(primes),'columns':a*(d+1),'rank_mod_p':r,'kernel_dimension_mod_p':a*(d+1)-r};print(row,flush=True);out.append(row)
(D/'outputs/macmahon.json').write_text(json.dumps({'modulus':P,'N':N,'results':out,'limit':'Only prime-vanishing linear-algebra diagnostics. No positivity, exact rational lift, table-span exclusion, or all-primes assertion.'},indent=2)+'\n')
