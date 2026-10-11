"""Exact finite checks of the geometric manuscript's algebraic interfaces."""
from fractions import Fraction as F
import itertools,json,random
rng=random.Random(13014);checks=0
for n in range(3,11):
 for _ in range(100):
  # Keep logarithmic volumes formal: V_D=(1-t)V_K+t V_L, trace=-slope.
  t=F(rng.randrange(1,20),20);vk=F(rng.randrange(-20,21));vl=F(rng.randrange(-20,21));vd=(1-t)*vk+t*vl;tr=vk-vl
  assert vd+t*tr==vk and vd-(1-t)*tr==vl;checks+=2
  a=F(rng.randrange(1,100));b=F(rng.randrange(1,100),100)
  theta=b/(8*(a+b+1));alpha=8*n*(n+2)/theta
  assert (F(1,2)-a/(8*(a+b+1)))>=F(3,8)>=2*theta
  assert theta/(8*n*(n+2))==1/alpha;checks+=2
 # Product boxes: a facet normal in block i scales area by det(T)/s_i.
 for dims in [(n,),(1,n-1),(1,1,n-2)]:
  s=[F(i+2,i+1) for i in range(len(dims))];det=F(1)
  for si,di in zip(s,dims):det*=si**di
  for i in range(len(dims)):
   area=F(1)
   for j,(sj,dj) in enumerate(zip(s,dims)):area*=sj**(dj-(i==j))
   assert area==det/s[i];checks+=1
 # Cone-cap integral, after removing kappa_(n-1).
 for r,H,eta in itertools.product([F(1,2),F(1)],[F(2),F(3)],[F(1,10),F(1,2)]):
  integral=(r/H)**(n-1)*eta**n/n
  assert integral==r**(n-1)*eta**n/(n*H**(n-1));checks+=1
# A radius-R sphere has p=1/R and full gradient norm=1/R,
# whereas its spherical gradient vanishes.
for n in range(3,11):
 for R in [F(1,2),F(1),F(3)]:
  p=1/R;gradnorm=1/R
  assert p**(-n)*gradnorm==R**(n-1);checks+=1
print(json.dumps({'status':'PASS','exact_assertions':checks,'scope':'finite rate balances, endpoint-volume signs, block area scaling and cone-cap formulas; does not verify compactness, PDE regularity or the assumed analytic inputs'},indent=2))
