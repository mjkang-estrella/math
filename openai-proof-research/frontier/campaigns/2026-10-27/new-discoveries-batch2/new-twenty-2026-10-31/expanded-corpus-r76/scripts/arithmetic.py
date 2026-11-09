from finite import *
def consecutive():
 N=20000; sp=list(range(N+101))
 for p in range(2,math.isqrt(len(sp))+1):
  if sp[p]==p:
   for q in range(p*p,len(sp),p):
    if sp[q]==q:sp[q]=p
 def fac(n):
  d={}
  while n>1:
   p=sp[n];d[p]=d.get(p,0)+1;n//=p
  return d
 tested=0;fails=[]
 for k in range(4,61):
  pk=next(p for p in range(k,k+100) if sp[p]==p)
  for n in range(max(0,pk-k),N+1):
   d={}
   for a in range(n+1,n+k+1):
    for p,e in fac(a).items():d[p]=d.get(p,0)+e
   tested+=1
   if not any(p>k and e==1 for p,e in d.items()):fails.append([n,k])
 save('consecutive-small.json',dict(n_max=N,k_min=4,k_max=60,tests=tested,counterexamples=fails,scope='All nonnegative n<=20000 meeting n+k>=least prime>=k; direct factorization of each product. Negative/zero-factor literal defects excluded.'))
def cyclotomic():
 # exact coefficient recurrence from product (1-x^pqr)(1-x^p)(1-x^q)(1-x^r) / ((1-x)(1-x^pq)(1-x^pr)(1-x^qr))
 ps=[p for p in range(3,101,2) if all(p%d for d in range(2,math.isqrt(p)+1))];out={};count=0;maxdeg=0
 for p,q,r in it.combinations(ps,3):
  n=p*q*r
  if n>30000:continue
  deg=(p-1)*(q-1)*(r-1);a=[1]+[0]*deg
  for k in [1,p*q,p*r,q*r]:
   for j in range(k,deg+1):a[j]+=a[j-k]
  for k in [p,q,r,n]:
   for j in range(deg,k-1,-1):a[j]-=a[j-k]
  h=max(map(abs,a));out[h]=min(out.get(h,n),n);count+=1;maxdeg=max(maxdeg,deg)
 save('cyclotomic-small.json',dict(primes='all odd primes <=100',product_max=30000,triples=count,max_degree=maxdeg,least_representatives_in_search=out,scope='Exact heights of finite ternary cyclotomic family only; no finite search refutes existence of absolute polynomial-growth constants.'))
if __name__=='__main__':globals()[sys.argv[1]]()
