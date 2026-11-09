# Source (Tokushige arXiv:2304.13466v3, Sec.1) family Q for t=2: Q={[t]∪A : A⊆[t+1,n], |A|>=n/2} ∪ {B∪[t+1,n] : B⊆[t]}.
# Exact p-biased measure vs the MathDB threshold max{p^t/2, mu(F1), mu(F2)} at p=3/5 <= p0(2)=2/(sqrt(17)-1).
from fractions import Fraction as F
from math import comb, ceil, sqrt
import json,sys
t=2; p=F(3,5); qq=1-p
assert float(p) <= 2/(sqrt(4*t+9)-1)
def muF(i): # F_i^t = {F : |F ∩ [t+3i]| >= t+2i}
  L=t+3*i; return sum(comb(L,j)*p**j*qq**(L-j) for j in range(t+2*i,L+1))
thr=max(p**t/2,muF(1),muF(2))
out=[]
for n in [20,40,60,80,100]:
  m=n-t; first=p**t*sum(comb(m,j)*p**j*qq**(m-j) for j in range(ceil(F(n,2)),m+1))
  second=p**(n-t)            # B∪[t+1,n], all B ⊆ [t]
  overlap=p**n if (n-t)>=F(n,2) else 0   # [n] counted twice
  mu=first+second-overlap
  out.append(dict(n=n,mu_Q=float(mu),threshold=float(thr),exceeds=mu>thr))
print(json.dumps(dict(t=t,p="3/5",mu_F1=float(muF(1)),mu_F2=float(muF(2)),half_p_t=float(p**t/2),rows=out),indent=1))
