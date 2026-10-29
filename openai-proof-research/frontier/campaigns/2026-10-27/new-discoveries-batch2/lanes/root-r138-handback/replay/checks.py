"""Exact bounded diagnostic controls; no universal partition claim is certified."""
import json,math,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent
N=5000
# Independent generating-product dynamic program and Euler recurrence.
p=[0]*(N+1);p[0]=1
for k in range(1,N+1):
 for n in range(k,N+1):p[n]+=p[n-k]
r=[1]
for n in range(1,N+1):
 total=0;k=1
 while k*(3*k-1)//2<=n:
  sign=1 if k%2 else -1;a=k*(3*k-1)//2;b=k*(3*k+1)//2
  total+=sign*r[n-a]
  if b<=n:total+=sign*r[n-b]
  k+=1
 r.append(total)
assert r==p
primes=[]
for q in range(2,N+1):
 if all(q%d for d in range(2,math.isqrt(q)+1)):primes.append(q)
def vfac(n,q):
 s=0
 while n:n//=q;s+=n
 return s
facts=1;hits=[];small_defects=[];large_residual=[]
for n in range(1,N+1):
 facts*=n
 hit=facts%p[n]==0
 if hit:hits.append(n)
 rem=p[n];defects=[]
 for q in primes:
  if q>n:break
  a=0
  while rem%q==0:rem//=q;a+=1
  if a>vfac(n,q):defects.append([q,a,vfac(n,q)])
 assert hit==(rem==1 and not defects)
 if n>=4096:
  assert not any(q*q<=n for q,a,b in defects)
  if rem!=1:large_residual.append(n)
 if defects:small_defects.append([n,defects])
S=[1,2,3,7,9,10,11,12,14,15,16,17,18,19,20,21,24,28,32,33,39]
assert hits==S
# A countermodel to a growth-only proof: smooth exp(Theta(sqrt(n))) integers divide n!.
for n in range(4,N+1):assert vfac(n,2)>=math.isqrt(n)
out=dict(status='PASS',N=N,independent_partition_entries=N+1,exact_divisibility_and_valuation_cases=N,hits=hits,valuation_defects=small_defects,large_residual_count_after_4095=len(large_residual),smooth_growth_controls=N-3,partition_array_sha256=hashlib.sha256(json.dumps(p).encode()).hexdigest(),scope='Finite controls only; neither extends the published 2,000,000 search nor proves a universal result.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='valuation_defects'})
