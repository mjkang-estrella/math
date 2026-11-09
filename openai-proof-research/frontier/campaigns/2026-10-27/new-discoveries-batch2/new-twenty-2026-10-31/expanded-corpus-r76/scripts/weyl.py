from finite import *
def partitions(n,m=None):
 if n==0:yield ();return
 for k in range(min(n,m or n),1-1,-1):
  for a in partitions(n-k,k):yield(k,)+a
parts=[p for n in range(5) for p in partitions(n)]
counts=[];fails=[]
for n in range(2,7):
 perms=[(p,sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))) for p in it.permutations(range(n))]
 tests=0
 for l,r in it.product(parts,repeat=2):
  if len(l)+len(r)>n:continue
  mu=l+(0,)*(n-len(l)-len(r))+tuple(-x for x in reversed(r))
  deg=sum(mu);a=[n*(n-1-2*i+2*mu[i])-2*deg for i in range(n)] # 2n times weight
  bad=set()
  for p,q in perms:
   s=0
   for k in range(n-1):
    s+=a[p[k]]
    if s<=0:bad.add(q);break
  actual=max(q for q in range(n*(n-1)//2+1) if q not in bad)
  pred=next(i+1 for i in range(n) if a[i]<=0 or a[n-1-i]>=0)-2
  tests+=1
  if actual!=pred:fails.append(dict(n=n,left=l,right=r,weight_scaled=a,actual=actual,predicted=pred))
 counts.append(dict(n=n,bipartitions=tests,permutations_per_bipartition=len(perms)))
save('weyl-small.json',dict(definition='Source (3.3.1)-(3.3.2): literal max over good exact Coxeter-length layers, positivity of every proper partial sum. Integer weight scaled by2n.',part_size_max_each=4,coverage=counts,failures=fails))
