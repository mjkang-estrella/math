"""Exact checks only. The universal deduction is documented separately."""
import math,json
from fractions import Fraction as F
from pathlib import Path
checked=0;primecases=0;compositecases=0
isprime=lambda n:n>=2 and all(n%k for k in range(2,math.isqrt(n)+1))
for d in range(2,61):
 for m in range(2,16):
  n=d*m-1;mod=n*n;fac=math.factorial(n-1);fk=1;pk=1;N=0
  for k in range(n):
   if k:
    fk*=k;j=k-1
    pk=pk*(d*j+1-d)*(d*j+1)*pow(d*j+1+d,d-2,mod)%mod
   N=(N+pow(fac//fk,d,mod)*pow(d,d*(n-1-k),mod)*pk)%mod
  assert N==0,(d,n,N)
  checked+=1
  if isprime(n):primecases+=1
  else:compositecases+=1
for n in range(3,60,2):
 term=F(1);s=term
 for k in range(1,n):term*=F(2*k-3,2)*F(2*k-1,2)/(k*k);s+=term
 central=F(math.comb(2*n-2,n-1),4**(n-1))
 assert s==(2*n-1)*central**2
 value=s*F(math.factorial(n-1)**2*2**(2*n-2),n*n)
 oddprod=math.prod(range(1,2*n-2,2));assert oddprod%n==0
 assert value==(2*n-1)*(oddprod//n)**2
out={'status':'PASS','exact_modular_scaled_numerator_cases':checked,'prime_cases':primecases,'composite_cases':compositecases,'d2_exact_formula_cases':29,'finite_checks_not_universal_proof':True,'credit':0}
Path(__file__).with_name('integrality-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
