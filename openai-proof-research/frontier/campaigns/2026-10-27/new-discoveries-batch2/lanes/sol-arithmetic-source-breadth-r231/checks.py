"""Exact controls. Run only through the assigned helper_guard.py."""
import json
from pathlib import Path
from fractions import Fraction
L=Path(__file__).resolve().parent
def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  a<<=1;b>>=1
 return r
def rem(a,b):
 while a.bit_length()>=b.bit_length():a^=b<<(a.bit_length()-b.bit_length())
 return a
def gcd(a,b):
 while b:a,b=b,rem(a,b)
 return a
def irreducible(f):
 n=f.bit_length()-1;x=2
 for j in range(1,n+1):
  x=rem(mul(x,x),f)
  if j<=n//2 and gcd(x^2,f)!=1:return False
 return x==2
def prime(u):return u>=2 and all(u%j for j in range(2,int(u**.5)+1))
def primitive(u):
 if not prime(u):return False
 x=1
 for j in range(1,u):
  x=2*x%u
  if x==1:return j==u-1
 raise AssertionError
rows=[]
for u in range(3,152,2):
 r=0;power=1
 for j in range(u):r^=power;power=mul(power,7)
 got=irreducible(r);want=primitive(u);assert got==want,(u,got,want)
 rows.append({'u':u,'degree':r.bit_length()-1,'irreducible':got})
# Independent Frobenius orbit certificate for every primitive-root case.
orbits=[]
for row in rows:
 if not row['irreducible']:continue
 u=row['u'];phi=(1<<u)-1;alpha=2;t=0
 for j in range(u-1):t^=alpha;alpha=rem(mul(alpha,alpha),phi)
 assert t==1 and alpha==2
 orbits.append(u)
# Independent source-fidelity control of the already-public HMT refutation.
xs=[Fraction(3**85,85),Fraction(3**84,28),Fraction(3**81)]
def vp(n,p):
 k=0
 while n%p==0:n//=p;k+=1
 return k
assert len(set(xs))==3
for x in xs:assert x*Fraction(vp(x.numerator,3)-vp(x.denominator,3),3)==3**84
result={'gf2_odd_u_3_through_151':rows,'primitive_root_trace_controls':orbits,
 'public_derivative_counterexample':{'p':3,'target':'3^84','solutions':['3^85/85','3^84/28','3^81']},
 'scope':'Exact finite controls only; universal polynomial proof is in PROOF.md; derivative question already public.'}
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'polynomial_cases':len(rows),'trace_cases':len(orbits),'derivative_controls':3,'pass':True}))
