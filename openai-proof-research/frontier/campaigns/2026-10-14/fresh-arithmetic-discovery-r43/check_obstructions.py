"""Finite exact arithmetic support, not proof of the limsup target."""
from fractions import Fraction as F
from math import gcd
import json

def require(x,msg):
 if not x:raise ValueError(msg)
def mul(x,y):
 a,b=x;c,d=y
 return (a*c+b*d,a*d+b*c-b*d) # gamma^2=1-gamma
f=[0,1]
for _ in range(60):f.append(f[-1]+f[-2])
count=0;rows=[]
for j in range(6,61,6):
 k,l=f[j],f[j-1];n=k+1
 z=(1,0)
 for _ in range(j):z=mul(z,(0,1))
 require(z==(l,-k),'Fibonacci quadratic-field identity');count+=1
 require(gcd(l,n)==1 and l%2==1,'primitive n,l');count+=1
 for p in [101,103,107,109]:
  if n*l%p==0:continue
  good=[a for a in range(p) if gcd(a,p)==1 and gcd(n*a+l,p*n)==1]
  require(len(good)==p-2,'exact primitive pair count');count+=1
  require(all(0<n*a+l<p*n for a in good),'center numerator range');count+=1
  require(3*(p-2)*p >= (p-1)**2,'ratio lower bound');count+=1
 rows.append({'j':j,'k':k,'l':l,'n':n})
a,n0=f[12],f[11]
primes=[p for p in range(3,1000) if all(p%d for d in range(2,int(p**.5)+1)) and a*n0%p]
ratio=F(1)
for p in primes:
 bad=(-n0*pow(a,-1,p))%p
 require(bad!=0,'distinct exclusions');count+=1
 survivors=sum(b!=0 and b!=bad for b in range(p))
 require(survivors==p-2,'CRT local density');count+=1
 ratio*=F(p-2,p-1)
print(json.dumps({'status':'PASS_FINITE_ARITHMETIC','assertions':count,'fibonacci_cases':rows,'extra_sieve_prime_count':len(primes),'extra_sieve_ratio':str(ratio),'limits':'These finite checks do not establish the limsup target, infinite Euler-product limit, or any modified source-array estimate.'},indent=2))
