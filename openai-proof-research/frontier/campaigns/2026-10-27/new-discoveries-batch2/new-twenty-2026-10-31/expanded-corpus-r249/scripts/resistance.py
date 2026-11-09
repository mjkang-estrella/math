import pathlib,json,fractions
F=fractions.Fraction;L=pathlib.Path(__file__).resolve().parents[1]
def R(n,k):
 N=n-1;A=[[F(0) for _ in range(N)] for _ in range(N)];b=[F(int(i==0)) for i in range(N)]
 for i in range(N):
  A[i][i]=min(k,i)+min(k,n-1-i)
  for j in range(max(0,i-k),min(N,i+k+1)):
   if i!=j:A[i][j]=F(-1)
 for i in range(N):
  for j in range(i+1,min(N,i+k+1)):
   if not A[j][i]:continue
   m=A[j][i]/A[i][i];A[j][i]=F(0);b[j]-=m*b[i]
   for h in range(i+1,min(N,i+k+1)):A[j][h]-=m*A[i][h]
 x=[F(0)]*N
 for i in reversed(range(N)):x[i]=(b[i]-sum(A[i][j]*x[j] for j in range(i+1,min(N,i+k+1))))/A[i][i]
 return x[0]
out=[]
for k in range(1,9):
 for n in [12,20,40,60]:
  a=R(n,k);b=R(n+1,k);d=b-a;target=F(6,k*(k+1)*(2*k+1));r=dict(k=k,n=n,resistance=str(a),increment=str(d),conjectured_limit=str(target),absolute_error=str(abs(d-target)));out.append(r);print(k,n,float(d),float(abs(d-target)),flush=True)
(L/'resistance-results.json').write_text(json.dumps(out,indent=2))
