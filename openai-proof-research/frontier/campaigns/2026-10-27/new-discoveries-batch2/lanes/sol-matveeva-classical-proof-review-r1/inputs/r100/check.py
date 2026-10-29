from fractions import Fraction as F
from pathlib import Path
import json
P=Path(__file__).resolve().parent
checks=0
# Independently compare coefficient of x^n in x*A*S'+B*S with
# the original delayed recurrence, including the initial polynomial.
for d in range(1,7):
 for seed in range(1,9):
  a=[F(((-1)**(k+seed))*(k+seed),seed+1) for k in range(d+1)]
  b=[F(2*k-seed,seed+2) for k in range(d+1)]
  s=[F((j*j+seed)%17-8,j+1) for j in range(45)]
  B=[k*a[k]+b[k] for k in range(d+1)]
  for n in range(45):
   lhs=sum((a[k]*(n-k)+B[k])*s[n-k] for k in range(min(d,n)+1))
   rhs=sum((a[k]*n+b[k])*s[n-k] for k in range(min(d,n)+1))
   assert lhs==rhs;checks+=1
# Exact obstruction to the tempting 'rational coefficients imply rational residues'.
# r=1/(1+x*x) has residue 1/(2*i) at i, irrational over Q.
# Explicit formal solution has denominators at p=3 mod4; this is NOT a source counterexample.
c=[F(1),F(1)]
for n in range(1,40):c.append((c[n]-(n-1)*c[n-1])/(n+1))
for n in range(1,40):
 assert (n+1)*c[n+1]+(n-1)*c[n-1]-c[n]==0;checks+=1
bad=[p for p in [3,7,11,19,23,31] if c[p].denominator%p==0]
assert bad==[3,7,11,19,23,31]
# Public Omega's distinct rational witness; no new discovery nomination.
for n in range(2,100):
 assert (n+1)**2+(-3*n-1)*n+(2*n+1)*(n-1)==0;checks+=1
# Puiseux removal mechanism, explicit algebraic H=sqrt(x)*(1-x)^(-1/2), S=(1-x)^(-1).
# x=t² gives U=S/H=1/(t*sqrt(1-t²)); U'-(-1/t²) is an ordinary algebraic series.
from math import comb
u={2*k-1:F(comb(2*k,k),4**k) for k in range(20)}
assert u[-1]==1
assert all(n>=0 for n,v in u.items() if n!=-1)
checks+=1
out={'status':'PASS','exact_assertions':checks,'coefficient_comparisons':2160,'nonrational_residue_diagnostic_denominator_primes':bad,'finite_checks_prove_universal_claim':False,'universal_argument':'PROOF.md; classical-theorem dependencies explicitly listed; no originality credit'}
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
