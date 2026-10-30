from fractions import Fraction as F
import json,itertools
# Exact rational controls of the already-public two-support-point bound.
controls=0
for m in range(2,31):
 threshold=F(m,m+1)
 for i in range(101):
  u=F(m-1,m)+F(i,100*m)
  a=F(2)/(2-u); b=F(2)/(2-m+m*u)
  assert max(a,b)>=F(2*m+2,m+2)
  controls+=1
 assert F(2)/(2-threshold)==F(2*m+2,m+2)
# Public mixed-radix recurrence, including its exact two-step identity.
radix=0
for ds in itertools.product(range(2,5),repeat=7):
 D=F(0);previous=F(0)
 for j,d in enumerate(ds):
  old=D; D=(1-D)/d
  assert 0<D<=F(1,2)
  if j: assert D==F(ds[j-1]-1,ds[j-1]*d)+previous/(ds[j-1]*d)
  previous=old;radix+=1
# Literal small-k capture exception: diagnostic only, no discovery credit.
k=2;x=[None,0,1]
for n in range(3,31):x.append((x[-1]+x[n-k]**2)%3)
assert all(x[n+4]==x[n] for n in range(1,27))
r=next(r for r in range(k+1,20) if x[r]==x[r+4]==0 and all(x[j]!=0 for j in range(r+1,r+4)))
assert r+4==9
print(json.dumps(dict(support_point_controls=controls,radix_steps=radix,finch_k2=dict(mu=0,z=r+4,difference=r+4),status='PASS',limit='Finite controls are not a universal source proof'),sort_keys=True))
