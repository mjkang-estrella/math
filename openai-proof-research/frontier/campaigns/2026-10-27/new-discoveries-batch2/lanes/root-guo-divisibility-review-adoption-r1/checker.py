"""Independent diagnostic: interpolation from values, not candidate recurrence."""
from pathlib import Path
from fractions import Fraction as F
from math import comb,prod,factorial
import json,datetime
H=Path(__file__).resolve().parent
counts={}
def tick(n):counts[n]=counts.get(n,0)+1
def C(a,b):return comb(a,b) if 0<=b<=a else 0
def odd(t):return prod(range(1,2*t+2,2))
def interp(k,r):
    # Exact Newton divided differences at squared odd integer nodes.
    nodes=[(2*(k+i)+1)**2 for i in range(r+1)]
    vals=[F(z**r) for z in nodes];out=[vals[0]]
    for j in range(1,r+1):
        vals=[(vals[i+1]-vals[i])/(nodes[i+j]-nodes[i]) for i in range(len(vals)-1)]
        out.append(vals[0])
    assert all(a.denominator==1 for a in out)
    return [int(a) for a in out]
for k in range(21):
 for r in range(14):
  a=interp(k,r)
  for m in range(k,k+19):
   z=(2*m+1)**2
   assert sum(a[t]*prod(z-(2*(k+i)+1)**2 for i in range(t)) for t in range(r+1))==z**r
   tick('interpolated_polynomial_values')
  for t in range(r+1):
   q=k+t
   for m in [k,q-1,q,q+1,q+7]:
    if m<k:continue
    lhs=prod((2*m+1)**2-(2*(k+i)+1)**2 for i in range(t))*C(m+k,2*k)
    rhs=4**t*factorial(2*q)//factorial(2*k)*C(m+q,2*q)
    assert lhs==rhs;tick('basis_cancellation_including_zeros')
   coefficient=F(odd(r)*4**t*C(2*k,k)*prod((k+i)**2 for i in range(1,t+1)),q+1)
   assert coefficient.denominator==1;tick('weighted_coefficient_integrality')
  for n in range(1,36):
   if k>=n:continue
   direct=sum((2*m+1)**(2*r+1)*C(m+k,2*k)*C(2*k,k)**2 for m in range(k,n))
   normalized=sum(F(a[t]*4**t*C(2*k,k)*prod((k+i)**2 for i in range(1,t+1)),k+t+1)*C(n-1,k+t)*C(n+k+t,k+t) for t in range(r+1))
   assert F(direct,n*n)==normalized
   assert odd(r)*direct%(n*n)==0;tick('literal_source_and_rational_expansion')
for q in range(60):
 for n in range(1,70):
  s=sum((2*m+1)*C(m+q,2*q) for m in range(q,n))
  endpoint=F(n*n*factorial(q)**2,(q+1)*factorial(2*q))*C(n-1,q)*C(n+q,q)
  assert s==endpoint;tick('telescoping_including_q_ge_n')
def vp(n,p):
 a=0
 while n%p==0:n//=p;a+=1
 return a
def prime(p):return p>=2 and all(p%d for d in range(2,int(p**.5)+1))
for k in range(201):
 for t in range(61):
  assert 4**t*odd(t)*C(2*k,k)%(k+t+1)==0;tick('denominator_grid')
# Adversarial d=p^a including huge k, t=0, p=2, a beyond floor(log_p(2t+1)).
for p in [2,3,5,7,11,13,17,31]:
 assert prime(p)
 for exponent in range(1,10):
  d=p**exponent
  for t in sorted({0,1,2,3,7,15,31,63,min(d-1,100),min(d-1,200)}):
   if t>=d:continue
   k=d-t-1;b=0
   while p**(b+1)<=2*t+1:b+=1
   # Factorial-floor valuation avoids constructing astronomically large central binomials.
   v=0;power=p
   while power<=2*k:
    term=(2*k)//power-2*(k//power);assert term in [0,1]
    if power>2*t+1 and power<=d:assert term==1
    v+=term;power*=p
   assert v>=max(0,exponent-b)
   complement=2*t if p==2 else sum(vp(i,p) for i in range(1,2*t+2,2))
   assert complement>=b and complement+v>=exponent;tick('targeted_prime_power_valuation')
assert sum((2*m+1)**3*C(m+1,2)*4 for m in range(1,3))==1608
assert 1608%9==6
result=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',method='Exact rational divided-difference interpolation and direct literal sums; independent of candidate code',counts=counts,limit='Finite diagnostics only. Universal proof in review.md is separate.',negative_control={'l':2,'n':3,'k':1,'unweighted_sum':1608,'residue_mod_9':6})
(H/'checker-evidence.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
