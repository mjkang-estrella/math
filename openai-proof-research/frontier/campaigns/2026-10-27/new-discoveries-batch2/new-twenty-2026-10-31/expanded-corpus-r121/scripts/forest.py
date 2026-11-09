import random,json,itertools
rng=random.Random(121)
def det(A):
 a=[r[:] for r in A];d=1;sgn=1;n=len(a)
 for k in range(n-1):
  if not a[k][k]:
   j=next((j for j in range(k+1,n) if a[j][k]),None)
   if j is None:return 0
   a[k],a[j]=a[j],a[k];sgn=-sgn
  q=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    z=a[i][j]*q-a[i][k]*a[k][j];assert z%d==0;a[i][j]=z//d
   a[i][k]=0
  d=q
 return sgn*a[-1][-1]
for p,q,x in itertools.product([1,2,3,5],[1,2,3,5],[1,2,10]):
 rows=[[1]]
 for n in range(1,33):
  b=sum(p**j*q**(n-2-j) for j in range(n-1));old=rows[-1]
  rows.append([(old[k-1] if k else 0)+(b*old[k] if k<len(old) else 0) for k in range(n+1)])
 moments=[sum(c*(p*q)**(k*(k-1)//2)*x**k for k,c in enumerate(row)) for row in rows]
 tested=neg=0
 for size in range(2,13):
  for t in range(10):
   I=list(range(size)) if t==0 else sorted(rng.sample(range(17),size));J=list(range(size)) if t==0 else sorted(rng.sample(range(17),size))
   d=det([[moments[i+j] for j in J] for i in I]);tested+=1
   if d<0:neg+=1;print('NEGATIVE',p,q,x,I,J,d,flush=True)
 print(json.dumps(dict(p=p,q=q,x=x,gamma=1,z=1,moment_max=32,minor_sizes=[2,12],tested=tested,negative=neg)),flush=True)
