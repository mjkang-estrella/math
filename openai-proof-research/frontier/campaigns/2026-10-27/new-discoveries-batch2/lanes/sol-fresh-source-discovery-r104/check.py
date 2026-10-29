from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
P=Path(__file__).resolve().parent
checks=0;rows=[]
def det(a):
 a=[r[:] for r in a];d=F(1)
 for i in range(len(a)):
  j=next((j for j in range(i,len(a)) if a[j][i]),None)
  if j is None:return 0
  if j!=i:a[i],a[j]=a[j],a[i];d=-d
  z=a[i][i];d*=z;a[i]=[x/z for x in a[i]]
  for j in range(i+1,len(a)):
   z=a[j][i];a[j]=[x-z*y for x,y in zip(a[j],a[i])]
 return d
for n in range(2,11):
 for v in [[F(1,n)]*n,[F(1,2),F(1,2)]+[F(0)]*(n-2),[F(i+1,n*(n+1)//2) for i in range(n)], [F(2),F(-1)]+[F(0)]*(n-2)]:
  L=[[2*F(i==j)-v[j] for j in range(n)] for i in range(n)]
  assert det(L)==2**(n-1);checks+=1
  points={tuple([F(1)]*n)};zeros=0
  for tail in product([-1,1],repeat=n-1):
   eps=(1,)+tail;a=sum(x*y for x,y in zip(v,eps))
   if not a:zeros+=1
   x=tuple(1-e*a for e in eps);points.add(x)
   assert all(x[i]**2==sum(L[i][j]*x[j] for j in range(n)) for i in range(n));checks+=1
  assert len(points)==1+2**(n-1)-zeros;assert len(points)>=1+2**(n-2);checks+=2
  if v==[F(1,2),F(1,2)]+[F(0)]*(n-2):assert len(points)==1+2**(n-2);checks+=1
  rows.append({'n':n,'v':[str(x) for x in v],'distinct_points':len(points),'zero_sign_pairs':zeros})
# Triangular all-complex extension cannot discard a preceding solution.
# x_1 in {0,1}; x_2^2-x_2+c*x_1^2=0: c=1 has two
# nonreal roots over x_1=1, so real filtering is unavailable.
assert 1-4*F(1)<0;checks+=1
out={'status':'PASS','assertions':checks,'rank_one_families':rows,'limits':'Exact verification of parametrized identities and route obstruction only; not a Conjecture6 solution or exhaustive classification.'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({'status':'PASS','assertions':checks,'families':len(rows)}))
