from math import comb,gcd,isqrt
from collections import Counter
import json,pathlib,random
r=pathlib.Path(__file__).resolve().parent
primes=[]
for p in range(2,10001):
 if all(p%q for q in primes if q*q<=p):primes.append(p)
def factors(x):
 out=[]
 for p in primes:
  if p*p>x:break
  if x%p==0:
   out.append(p)
   while x%p==0:x//=p
 if x>1:out.append(x)
 return out
def val(N,K,p):
 v=0
 while N:
  N//=p;K//=p
  # separate factorial valuations below used instead
  v+=N-K
 return v
def vpbin(N,K,p):
 L=N-K;v=0
 while N:
  N//=p;K//=p;L//=p;v+=N-K-L
 return v
def good(n,m):
 return all(vpbin(m*n*n,m*n,p)==0 for p in factors(m*(n-1)+1))
def lucas_zero(N,K,p):
 while N or K:
  if K%p>N%p:return True
  N//=p;K//=p
 return False
small=0
for n in range(1,81):
 for m in range(1,21):
  d=m*(n-1)+1;B=comb(m*n*n,m*n)
  assert good(n,m)==(gcd(B,d)==1)
  for p in factors(d):assert lucas_zero(m*n*n,m*n,p)==(vpbin(m*n*n,m*n,p)>0)
  small+=1
expected=[1,2,2,2,2,2,2,4,2,2,2,2,2,2,2,2,3,6,2,2,2,2,3,2,2,4,2,2,2,2,2,10,3,2,3,2,2,4,5,2]
records=[];maxm=0;counts=Counter();primelem=0;worst=(0,1,0)
for n in range(1,100001):
 m=1
 while not good(n,m):m+=1
 if n<=len(expected):assert m==expected[n-1]
 assert m*m<=3*n+4
 counts[m]+=1
 if m>maxm:records.append([n,m]);maxm=m
 if m*m*worst[1]>worst[0]*(3*n+4):worst=(m*m,3*n+4,n)
 for j in range(2,min(12,n)+1):
  d=j*(n-1)+1
  if len(factors(d))==1 and factors(d)[0]==d:
   assert good(n,j);primelem+=1
# All m<=B can fail to produce prime modulus: composite witnesses are essential.
primefree=[]
for n in range(3,2001):
 B=isqrt(3*n+4)
 if all(len(factors(m*(n-1)+1))!=1 or factors(m*(n-1)+1)[0]!=m*(n-1)+1 for m in range(2,B+1)):
  primefree.append(n)
# m=1 never works for n>1: n divides C(n²,n), since C(n²,n)=n*C(n²-1,n-1).
for n in range(2,100):assert comb(n*n,n)%n==0 and not good(n,1)
report={'literal_comparisons':small,'scan_n':100000,'record_minima':records,'counts':dict(sorted(counts.items())),'max_ratio_squared':worst,'prime_modulus_lemma_tests':primelem,'first_primefree_n':primefree[:20],'primefree_count_through_2000':len(primefree)}
(r/'checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
