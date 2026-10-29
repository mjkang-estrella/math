import math,itertools,json,pathlib
from fractions import Fraction as F
L=pathlib.Path(__file__).resolve().parent

def det(a):
 a=[list(map(F,r)) for r in a];v=F(1)
 for j in range(len(a)):
  p=next((i for i in range(j,len(a)) if a[i][j]),None)
  if p is None:return 0
  if p!=j:a[p],a[j]=a[j],a[p];v=-v
  t=a[j][j];v*=t
  for i in range(j+1,len(a)):
   q=a[i][j]/t
   for k in range(j+1,len(a)):a[i][k]-=q*a[j][k]
 return v

def b(m,n,k):return math.comb(n,k)*math.comb(m*n,n-k) if 0<=k<=n else 0
def a(m,n,k):return F(math.comb(n+1,k)*math.comb(m*(n+1),n-k),n+1) if 0<=k<=n else 0
counts={};fail=[];ident=0
for m in range(2,9):
 for name,f in [('A',a),('B',b)]:
  for kind in ['triangle','reverse','square']:
   fun=lambda n,k: f(m,n+k,k) if kind=='square' else f(m,n,n-k) if kind=='reverse' else f(m,n,k)
   count=0
   for r in range(1,5):
    for rows in itertools.combinations(range(7),r):
     for cols in itertools.combinations(range(7),r):
      d=det([[fun(n,k) for k in cols] for n in rows]);count+=1
      if d<0 or (kind=='square' and d==0):fail.append([m,name,kind,rows,cols,str(d)])
   counts[f'{m}/{name}/{kind}']=count
  for n in range(9):
   for k in range(9):
    q=math.prod(k+j for j in range(1,n+1))*math.prod(m*(n+k)-j for j in range(n))
    assert F(q,math.factorial(n)**2)==b(m,n+k,k);ident+=1
# production matrix for B, positive diagonal triangular inversion
prodneg=[]
for m in range(2,6):
 N=9;T=[[F(b(m,n,k)) for k in range(N)] for n in range(N)]
 P=[[F(b(m,n+1,k)) for k in range(N)] for n in range(N)]
 for n in range(N):
  for j in range(n):
   for k in range(N):P[n][k]-=T[n][j]*P[j][k]
 for n in range(N):
  for k in range(N):
   if P[n][k]<0:prodneg.append([m,n,k,str(P[n][k])])
res={'literal_minor_checks':sum(counts.values()),'ranges':'m=2..8; six matrices; indices0..6; all minors orders1..4','failures':fail[:10],'polynomial_identities':ident,'negative_production_entries':prodneg[:15],'scope':'finite diagnostics only, not source proof'}
(L/'check-results.json').write_text(json.dumps(res,indent=2));print(json.dumps(res,indent=2))
