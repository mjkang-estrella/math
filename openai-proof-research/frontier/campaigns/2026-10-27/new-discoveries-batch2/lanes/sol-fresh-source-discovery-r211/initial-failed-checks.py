"""Exact finite diagnostics; no universal conclusion."""
import math,json
def primes(n):
 out=[]
 for a in range(2,n+1):
  if all(a%p for p in out if p*p<=a):out.append(a)
 return out
def root(x,k):
 if k==2:return math.isqrt(x)
 lo=0;hi=1<<((x.bit_length()+k-1)//k)
 while lo+1<hi:
  m=(lo+hi)//2
  if m**k<=x:lo=m
  else:hi=m
 return hi if hi**k<=x else lo
P=primes(4000); rows=[];tested=0
for n in range(8,501):
 f=math.factorial(n);best=None
 for k in P:
  if 2**k>f+n:break
  m=root(f,k)
  assert m**k<=f<(m+1)**k
  d=min(abs(f-m**k),abs(f-(m+1)**k));tested+=1
  assert d>n,(n,k,m,d)
  if best is None or d<best[0]:best=(d,k,m)
 rows.append(dict(n=n,minimum_distance=str(best[0]),prime_exponent=best[1],floor_root=str(best[2])))
# Independent exhaustive prime-power partitions of the square route.
partitions=0;cases=0;solutions=[]
for n in range(4,46):
 f=math.factorial(n)
 for a in range(1,math.isqrt(n)+1):
  if f%(4*a*a):continue
  N=f//(4*a*a);t=N;blocks=[]
  for p in P:
   if p>n:break
   q=1
   while t%p==0:t//=p;q*=p
   if q>1:blocks.append(q)
  assert t==1
  ds=[1]
  for q in blocks:ds += [d*q for d in ds]
  cases+=1
  for u in ds:
   partitions+=1;v=N//u
   assert u*v==N and math.gcd(u,v)==1
   if v==u+1:
    b=2*u+1;assert f==a*a*(b*b-1);solutions.append([n,a,b])
  b=math.isqrt(f//(a*a)+1)
  direct=(b*b==f//(a*a)+1)
  assert direct==any(N//u==u+1 for u in ds)
assert solutions==[[4,1,5],[5,1,11],[7,1,71]],solutions
# Finite local-congruence controls of the written all-modulus obstruction.
for M in range(2,201):
 assert math.factorial(M)%M==0
 assert (math.factorial(M)+1)%M==pow(1,2,M)
# Exact falsifier for Maiti v2 Section2.15 floor identity (not for Brocard).
n=3;k=math.isqrt(math.factorial(n));lhs=math.isqrt(math.factorial(n+1));rhs=math.isqrt(k*k*(n+1))
assert (lhs,rhs)==(4,3)
print(json.dumps(dict(status='PASS',scope='all perfect powers for 8<=n<=500 only; square partitions 4<=n<=45 only',prime_exponent_tests=tested,square_partition_cases=cases,square_partitions=partitions,square_controls=solutions,maiti_floor_identity_falsifier=dict(n=n,left=lhs,right=rhs),rows=rows),indent=2))
