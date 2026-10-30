from fractions import Fraction as F
from math import gcd,isqrt
import json
N=2500
rows=[];E=F(0);B=F(0);C=F(0);weighted=F(0)
for n in range(1,N+1):
 phi=sum(gcd(k,n)==1 for k in range(1,n+1))
 rem=n;ps=[];d=2
 while d*d<=rem:
  if rem%d==0:
   ps.append(d)
   while rem%d==0:rem//=d
  d+=1
 if rem>1:ps.append(rem)
 S=sum(p-1 for p in ps); R=F(phi-1-S,phi)
 assert S<=n-1 and R<1 and abs(R-1)==F(1+S,phi)
 assert 2*phi*phi>=n
 # Full squarefree divisor expansion of (n/phi(n))^2.
 expansion=F(1)
 for p in ps:expansion*=1+(F(p,p-1)**2-1)
 assert expansion==F(n,phi)**2
 E+=abs(R-1);B+=F(S,n);C+=F(n,phi)**2;weighted+=F(S,phi)
 if n in [1,2,4,10,100,1000,N]:
  assert weighted**2<=B*C # Cauchy plus (S/n)^2 <= S/n
  rows.append(dict(N=n,error_exact=str(E/n),error_float=float(E/n),mean_S_over_n=float(B/n),mean_square_n_over_phi=float(C/n)))
 # Nonintegral cutoffs reduce to floor X without endpoint change.
 assert (F(2*n+1,2).numerator//F(2*n+1,2).denominator)==n
print(json.dumps(dict(status='PASS',N=N,method='direct gcd totient, trial division support, exact Fraction divisor-moment/Cauchy controls',rows=rows,limits='Finite diagnostics only, not a limit proof.'),indent=2))
