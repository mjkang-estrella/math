from itertools import product
from math import comb
from collections import defaultdict

def data(n,k):
 # factor choices: 0 -> first endpoint in (n,j), or (i,1)
 edges=[(n-1,j) for j in range(k)]+[(i,0) for i in range(k,n-1)]
 groups=defaultdict(int)
 for bits in product(range(2),repeat=n-1):
  a=[0]*n;c=1
  for bit,(i,j) in zip(bits,edges):a[(i,j)[bit]]+=1;c*=(-1)**bit
  s=0;r=n
  for i in range(n-1):
   s+=a[i]
   if s<i+1:r=i+1;break
  groups[r]+=c
 v=sum(c*(-1)**(n-r)*comb(n-1,r-1) for r,c in groups.items())
 return v,dict(sorted(groups.items()))
for n in range(3,10):
 for k in range(1,n):
  v,g=data(n,k)
  print(n,k,v,g)
  assert v==(-1)**(n-1)*comb(n,k)*comb(n-2,k-1)
