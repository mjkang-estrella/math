import json,math,time
from pathlib import Path
L=Path(__file__).resolve().parent;start=time.monotonic()
def primes(b):
 return [p for p in range(2,b+1) if all(p%d for d in range(2,math.isqrt(p)+1))]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def rem(a,b,p):
 a=trim([x%p for x in a]);b=trim(b[:]);inv=pow(b[-1],-1,p)
 while len(a)>=len(b) and a!=[0]:
  z=a[-1]*inv%p;k=len(a)-len(b)
  for j in range(len(b)):a[j+k]=(a[j+k]-z*b[j])%p
  trim(a)
 return a
def mul(a,b,f,p):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
 return rem(c,f,p)
def power(a,k,f,p):
 b=[1]
 while k:
  if k&1:b=mul(b,a,f,p)
  a=mul(a,a,f,p);k//=2
 return b
def gcd(a,b,p):
 while b!=[0]:a,b=b,rem(a,b,p)
 return a
def subx(a,p):
 b=a[:]+[0]*max(0,2-len(a));b[1]=(b[1]-1)%p;return trim(b)
def irreducible(f,p):
 n=len(f)-1
 if n==1:return True
 checks={n//q for q in primes(n) if n%q==0};a=[0,1]
 for k in range(1,n+1):
  a=power(a,p,f,p)
  if k in checks and len(gcd(f,subx(a,p),p))>1:return False
 return subx(a,p)==[0]
C=[math.comb(2*k,k)//(k+1) for k in range(101)]
rows=[];trials=0
for n in range(1,41):
 f=C[:n+1][::-1]
 for p in primes(n*n+n+5):
  trials+=1
  if irreducible(f,p):rows.append(dict(n=n,least_prime=p,bound=n*n+n+5));break
 else:raise AssertionError(('source counterexample',n))
expected=[2,3,2,3,17,7,47,3,53,5,137,109,79,11,37,7,59,13,53,251,251,101,467,149,79,3,83,61,239,31,79,73,73,373,199,5,337,167,17,683]
assert [r['least_prime'] for r in rows]==expected
from sympy import Poly,Symbol
x=Symbol('x');independent=0
for r in rows:
 n=r['n'];p=r['least_prime'];f=Poly(sum(C[k]*x**(n-k) for k in range(n+1)),x,modulus=p)
 assert f.is_irreducible;independent+=1
 if n<=12:
  for q in primes(p-1):
   assert not Poly(sum(C[k]*x**(n-k) for k in range(n+1)),x,modulus=q).is_irreducible;independent+=1
local=0
for n in range(2,101):
 for p in primes(2*n):
  if p<=n+1:continue
  k=(p-1)//2;d=n-k
  # ascending coefficients of x^d Q_k
  f=C[:n+1][::-1];g=[0]*d+C[:k+1][::-1]
  assert [(a-b)%p for a,b in zip(f,g)]==[0]*(n+1)
  assert 0<d<n;local+=1
D=1+8*math.prod(primes(11));assert D==18481 and math.isqrt(D)**2!=D
for p in primes(11):assert D%p==1
frobenius=0
for p in primes(199):
 if p==2:continue
 k=(p-1)//2;f=C[:k+1][::-1];a=power([0,1],p,f,p)
 assert power(a,p,f,p)==rem([0,1],f,p);frobenius+=1
out=dict(result='PASS; diagnostics only',source_degrees=[1,40],rows=rows,rabin_trials=trials,independent_sympy_tests=independent,local_factorization_tests=local,local_degrees=[2,100],frobenius_square_tests=frobenius,generic_S2_obstruction_D=D,universal_source_result=False,seconds=time.monotonic()-start)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='rows'}))
