from fractions import Fraction
from itertools import combinations
for D in range(3,30,2):
 for r in range(1,min(D//2+1,5)):
  for tail in combinations(range(3,D+1,2),r):
   S=(1,)+tail
   # 1 trivial, so instead all odd k >=3
   for S in [tail]:
    a=[];c=[]
    for n in range(max(S)):
     T=[k for k in S if k<=n]
     v=1-sum((a[n-k] for k in T),Fraction(0))/len(T) if T else Fraction(0)
     a.append(v);c.append((-1)**n*(1-2*v))
    A=sum(sum(c[:k]) for k in S)/sum(S)
    if A<=0:print('nonpositive',S,A);raise SystemExit
print('all positive')
