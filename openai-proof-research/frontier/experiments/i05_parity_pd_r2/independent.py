#!/usr/bin/env python3
"""Exact independent tests; no numerical claim about asymptotic estimates."""
import json, math, itertools, fractions
from collections import defaultdict
from pathlib import Path
F=fractions.Fraction
HERE=Path(__file__).resolve().parent

def lam(n):
 s=1;p=2
 while p*p<=n:
  while n%p==0:n//=p;s=-s
  p+=1
 return -s if n>1 else s

def crt(a,m,b,n):
 return next((v for v in range(math.lcm(m,n)) if v%m==a%m and v%n==b%n),None)

out={}
# Actual determinant incidences mn-1=ah. Rational-complex pairs avoid floating arithmetic.
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conj(a):return a[0],-a[1]
count=overlaps=0
for bands in [((2,3),),((2,3),(5,7)),((2,3),(5,7),(11,13))]:
 K=len(bands);rows=defaultdict(list)
 for labels in itertools.product(*bands):
  a=math.prod(labels)
  for m in range(2,48):
   for n in range(2,43):
    if (m*n-1)%a:continue
    h=(m*n-1)//a
    alpha=(F(m%7-3,5),F(m%11-5,7));beta=(F(n%5-2,3),F(n%9-4,11))
    c=mul(alpha,beta);rows[h].append((a,c));overlaps+=math.gcd(a,h)>1
 for h,row in rows.items():
  unsigned=(F(0),F(0));signed=(F(0),F(0))
  for a,c in row:
   unsigned=add(unsigned,c);signed=add(signed,(lam(a*h)*c[0],lam(a*h)*c[1]))
  sign=(-1)**K*lam(h)
  assert signed==(sign*unsigned[0],sign*unsigned[1])
  assert mul(signed,conj(signed))==mul(unsigned,conj(unsigned))
  count+=1
out['actual_determinant_rows']={'h_rows':count,'selected_prime_overlap_incidences':overlaps,'failures':0}
# Source slots: shared count is J*s-sum|C_g|, not (J+1)*s-sum|C_g|.
count=repeat=0
for J in range(1,5):
 for s in range(1,4):
  for cvec in itertools.product(range(J+1),repeat=s):
   c=sum(cvec);nr=J*s-c
   for w in [1,2,4,6,12,25,49,75]:
    shared=[2 if i%2==0 else 3 for i in range(nr)]
    free=[5]*c
    dr=math.prod(shared);dc=math.prod(free)
    assert lam(dr*w)==(-1)**(J*s)*(-1)**c*lam(w)
    assert lam(dr)*lam(dc)==(-1)**(J*s)
    count+=1;repeat+=c>1 or nr>2
out['source_slot_sign']={'cases':count,'with_repetitions':repeat,'failures':0}
# Nonunit ordinary residue reduction is exact even when gcd(g,t)>1.
count=noncoprime=0
for k in range(1,65):
 for a in range(k):
  g=math.gcd(a,k)
  for n in range(1,201):
   lhs=n%k==a
   rhs=n%g==0 and (n//g)%(k//g)==(a//g)%(k//g)
   assert lhs==rhs
   if lhs:
    assert math.gcd(n//g,k//g)==1
    assert lam(n)==lam(g)*lam(n//g)
    noncoprime+=math.gcd(g,n//g)>1
   count+=1
out['ordinary_nonunit_reduction']={'cases':count,'overlapping_g_and_residual':noncoprime,'failures':0}
# SPR exact CRT, including all rejected overlaps. ell*d need only be a unit mod M.
count=rejectM=rejectD=nonunit=0
for M in range(1,33):
 for b in range(M):
  if math.gcd(b,M)>1:continue
  for r in range(1,33):
   for ld in [1,2,3,4,5,6,7,10,11,15,25,35]:
    if math.gcd(ld,M)>1:continue
    mod=math.lcm(r,M)
    solutions=[v for v in range(mod) if (ld*v+1)%r==0 and (ld*v+1-b)%M==0]
    if math.gcd(r,M)>1:
     assert solutions==[];rejectM+=1
    elif math.gcd(ld,r)>1:
     assert solutions==[];rejectD+=1
    else:
     assert len(solutions)==1
     a=solutions[0];g=math.gcd(b-1,M)
     assert math.gcd(a,r*M)==g
     assert math.gcd(a//g,r*M//g)==1
     for t in [a//g,a//g+r*M//g,a//g+2*r*M//g]:
      v=g*t
      assert (ld*v+1)%r==0 and (ld*v+1-b)%M==0
      if t:assert lam(ld*v)==lam(ld*g)*lam(t)
     nonunit+=g>1
    count+=1
out['SPR_CRT']={'cases':count,'incompatible_r_M':rejectM,'incompatible_r_ld':rejectD,'nonunit_a':nonunit,'failures':0}
# Exhaustive local density incl prime 2, prime powers in M, forced zeros.
primes=[2,3,5,7,11];count=forced=0
for M in range(1,81):
 for b in range(M):
  if math.gcd(b,M)>1:continue
  for q in primes:
   e=0;m=M
   while m%q==0:m//=q;e+=1
   rho=F(1,q*(q-1)) if e==0 else (F(1,q) if e==1 and b%q==1 else F(0)) if e==1 else F(int(b%(q*q)==1))
   mod=math.lcm(M,q*q)
   total=bad=0
   for a in range(b,mod,M):
    if math.gcd(a,mod)==1:
     total+=1;bad+=(a-1)%(q*q)==0
   assert F(bad,total)==rho
   forced+=rho==1;count+=1
out['local_square_densities']={'cases':count,'forced_zero_survival':forced,'failures':0}
# Exact size-biased sampling / factorial identity on labelled equal-mass balls.
count=0
for masses in [(F(1,2),F(1,4),F(1,4)),(F(1,3),)*3,(F(2,5),F(3,10),F(1,5),F(1,10))]:
 for sign in [-1,1]:
  for d in range(1,len(masses)+1):
   total=F(0)
   for labels in itertools.permutations(range(len(masses)),d):
    remaining=F(1);w=F(1)
    for j in labels:w*=masses[j]/remaining;remaining-=masses[j]
    total+=sign*w
    selected=sorted([masses[j] for j in labels],reverse=True)+[F(0)]*len(masses)
    full=sorted(masses,reverse=True)
    assert all(abs(full[i]-selected[i])<=remaining for i in range(len(masses)))
    count+=1
   assert total==sign
out['labelled_size_biased_total_mass_and_sorting']={'cases':count,'failures':0}
# All four limiting joint atoms follow by exact inversion of moments.
count=0
for C in [F(0),F(1,7),F(1,2),F(1)]:
 for h in [F(-2),F(0),F(3,7)]:
  atoms={(s,b):h*(C if b else 1-C)/2 for s in [-1,1] for b in [0,1]}
  assert sum(atoms.values())==h
  assert sum(s*v for (s,b),v in atoms.items())==0
  assert sum(b*v for (s,b),v in atoms.items())==C*h
  assert sum(s*b*v for (s,b),v in atoms.items())==0
  count+=1
out['four_joint_moment_inversion']={'cases':count,'failures':0}
out['scope']='Finite algebra only. These tests do not establish any analytic estimate or priority.'
(HERE/'independent-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
