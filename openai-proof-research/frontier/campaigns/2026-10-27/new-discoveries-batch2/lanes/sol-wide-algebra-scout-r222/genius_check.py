from fractions import Fraction as Q
import pathlib,json
L=pathlib.Path(__file__).resolve().parent
def mul(a,b,n):return [sum((a[j]*b[k-j] for j in range(k+1) if j<len(a) and k-j<len(b)),Q(0)) for k in range(n+1)]
def expx(d,n):
 a=[Q(1)]
 for k in range(1,n+1):a.append(sum((i*d[i]*a[k-i] for i in range(1,k+1)),Q(0))/k)
 return a
def expxy(u,d,n):
 a=[[Q(1)]+[Q(0)]*n]
 for k in range(1,n+1):
  row=[Q(0)]*(n+1)
  for i in range(1,k+1):
   for j in range(n+1):row[j]+=Q(i,k)*(d[i]*a[k-i][j]+(u[i]*a[k-i][j-1] if j else 0))
  a.append(row)
 return a[n]
rows=[]
for p in range(2,10):
 d=[Q(0)]+[Q((-1)**j,j+1) for j in range(1,p+1)];d[p]=0;d[p]=-expx(d,p)[p]
 a=expx(d,p);assert a[p]==0
 A=[Q(1)]+[Q(p,p-j)*a[j] for j in range(1,p)]
 u=[Q(0),Q(1)]+[Q(i+1,i+2) for i in range(2,p+1)]
 F=[Q(0)]*(p+1)
 for i in range(1,p+1):
  alpha=Q(i,p);b=[Q(1)]+[Q(0)]*(i-1);power=[Q(1)]+[Q(0)]*(i-1);binom=Q(1)
  for k in range(1,i):
   power=mul(power,[Q(0)]+A[1:],i-1);binom*=Q(alpha-k+1,k)
   b=[v+binom*w for v,w in zip(b,power)]
  F[i]=sum(j*u[j]*b[i-j] for j in range(1,i+1))/i
 lhs=expxy(u,d,p);rhs=expxy(F,[Q(0)]*(p+1),p);assert lhs==rhs
 rows.append(dict(p=p,status='exact PASS',F=[str(v) for v in F[1:]]))
(L/'genius-check.json').write_text(json.dumps(rows,indent=2));print(rows)
