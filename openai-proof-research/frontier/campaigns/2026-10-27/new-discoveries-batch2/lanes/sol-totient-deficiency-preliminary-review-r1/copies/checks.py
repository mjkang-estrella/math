from fractions import Fraction as F
from math import isqrt
import json
N=10000
phi=list(range(N+1));primes=[];support=[0]*(N+1);pf=[[] for _ in range(N+1)]
for p in range(2,N+1):
 if phi[p]==p:
  primes.append(p)
  for n in range(p,N+1,p):phi[n]-=phi[n]//p;support[n]+=p-1;pf[n].append(p)
phi[1]=1
terms1=[F(0)]*(N+1);terms2=[F(0)]*(N+1)
for n in range(1,N+1):
 assert 2*phi[n]**2>=n
 for p in pf[n]:
  m=n;a=0
  while m%p==0:m//=p;a+=1
  term=F(1,p**(a-1)*phi[m])
  assert term==F(p-1,phi[n])
  if a==1:terms1[n]+=term
  else:terms2[n]+=term
 assert terms1[n]+terms2[n]==F(support[n],phi[n])
rows=[]
for X in [1,10,100,1000,10000]:
 t1=sum(terms1[1:X+1],F(0));t2=sum(terms2[1:X+1],F(0));recip=sum((F(1,phi[m]) for m in range(1,X+1)),F(0))
 conv=sum((F(sum(p<=X//m for p in primes),phi[m]) for m in range(1,X+1)),F(0))
 assert t1<=conv;assert t2*t2<=36*X;assert recip*recip<=8*X
 err=(t1+t2+recip)/X
 bad=sum(F(1+support[n],phi[n])>F(1,2) for n in range(1,X+1))
 assert F(bad,X)<=2*err
 rows.append(dict(X=X,mean_absolute_error_exact=str(err),mean_absolute_error=float(err),half_error_count=bad))
print(json.dumps(dict(status='PASS',individual_exact_decompositions=N,cutoff_controls=rows,limits='Finite diagnostics only; universal proof is PROOF.md.'),indent=2))
