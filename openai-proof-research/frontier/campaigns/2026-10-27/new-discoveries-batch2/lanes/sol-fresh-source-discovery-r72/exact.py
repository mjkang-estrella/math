from fractions import Fraction as F
from collections import Counter
from itertools import product
import json,random,math
random.seed(722)
def dp(a):
 d=Counter({0:1})
 for x in a:
  e=Counter()
  for v,c in d.items():e[v-x]+=c;e[v+x]+=c
  d=e
 return d
checks=0
for n in range(1,9):
 for _ in range(20):
  a=[random.randint(1,6) for i in range(n)];d=dp(a);assert d==Counter(sum(x*y for x,y in zip(a,s)) for s in product([-1,1],repeat=n));checks+=1
  N=2**n;v=sum(x*x for x in a);m4=F(sum(x**4*c for x,c in d.items()),N)
  assert m4==3*v*v-2*sum(x**4 for x in a)
  dd=dp(a+a);m4new=F(sum(x**4*c for x,c in dd.items()),4*N*N)
  assert m4new-m4==sum(x**4 for x in a);checks+=2
# Laplace comparison for unnormalized weights(1,1): y=exp(-2t)
for j in range(1,100):
 y=F(j,100);L=F(3,8)+y/2+y**4/8-F(1,2)-y*y/2
 assert L==(y-1)**2*(y*y+2*y-1)/8;checks+=1
# Exact radical certificate single-coordinate splitting, p=5/2:
# A=(7-2sqrt2)*sqrt(2+2sqrt2), B=8sqrt2-2.
# Both positive. B^2-A^2=130-90sqrt2>0 since sqrt2<13/9.
assert 2*9**2<13**2;checks+=1
# Generic symmetric three-point law eps=2/5, z=9/8, p=2+2log2(z).
# z<sqrt2 implies 2<p<3; (1-eps)/z+eps*z=59/60<1.
e=F(2,5);z=F(9,8)
assert 1<z and z*z<2
ratio=(1-e)/z+e*z
assert ratio==F(59,60);checks+=2
# Strict subgaussian coefficient bound (infinite proof via recurrence in discovery.md).
for k in range(2,101):
 df=math.prod(range(1,2*k,2));assert e<=df*e**k;checks+=1
# n2 equal full doubling: z+z^3-2z^2=z(z-1)^2
for j in range(1,101):
 z=1+F(j,300);assert z+z**3-2*z*z==z*(z-1)**2>0;checks+=1
# Even binomial terms controlling off-support splitting all negative for p=5/2.
c=F(1)
for k in range(1,41):
 c*= (F(5,2)-k+1)/k
 if k>=4 and k%2==0:assert c<0;checks+=1
out={'status':'PASS','exact_assertions':checks,'independent_DP_vectors':160,'scope':'identities and method obstructions, no full-source proof','single_split_certificate':'sqrt(2)<13/9','generic_ratio':str(ratio)}
json.dump(out,open('exact.json','w'),indent=2);print(json.dumps(out))
