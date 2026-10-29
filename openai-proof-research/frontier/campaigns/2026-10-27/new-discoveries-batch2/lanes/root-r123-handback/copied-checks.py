from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
def df(k):
 r=1
 for x in range(1,2*k,2):r*=x
 return r
def moment(j):return sum((F(comb(j,k),4**j)*(F(1,2*k+3)-F(1,2*k+5)) for k in range(j+1)),F(0))
rows=[]
for n in range(3,43):
 u=-2*df(n)+(n+1)*factorial(n-1)*sum((F(df(k),factorial(k)) for k in range(n)),F(0))
 j=n-3;mixture=-F(factorial(2*j+5),8*factorial(j))*moment(j)
 assert u==mixture and u<0
 rows.append({'n':n,'u':str(u),'mixture':str(mixture)})
# The two integration-by-parts residual polynomials (z=s^2).
# A+e^{-z/2} combined under the integral yields z(1-3v^2)/4;
# d_v(v-v^3)e^{-z(1+v^2)/4} supplies z(v^2-v^4)/2.
for z in (F(1,7),F(1),F(13)):
 for v in (F(0),F(2,7),F(1)):
  original=z*(1-v*v)/4-1 +1-z*v*v/2
  assert original==z*(1-3*v*v)/4
  derivative=1-3*v*v-z*v*(v-v**3)/2
  assert 1-3*v*v-derivative==z*(v*v-v**4)/2
# Exact multiplicities of toy obstruction polynomials, NOT source densities.
def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def ev(p,x):return sum((a*x**i for i,a in enumerate(p)),F(0))
def deriv(p):return [i*p[i] for i in range(1,len(p))]
p=mul(mul([-1,1],[-1,1]),mul([-2,1],[-2,1]))
assert all(ev(p,F(t))==ev(deriv(p),F(t))==0 for t in (1,2))
q=mul(mul([-1,1],[-1,1]),mul([-1,1],[-1,1]))
assert ev(q,F(1))==ev(deriv(q),F(1))==ev(deriv(deriv(q)),F(1))==0
http=[]
for line in (L/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'copy' in r:
  data=(L/r['copy']).read_bytes();assert len(data)==r['bytes'] and hashlib.sha256(data).hexdigest()==r['sha256'];http.append(r['copy'])
assert not (L/'PROOF.md').exists()
print(json.dumps({'status':'PASS','exact_source_coefficient_rows':rows,'IBP_checks':9,'toy_obstructions_only':True,'HTTP_byte_bindings':http,'limits':'Finite rational checks support the recorded all-order routine argument. Toy functions do not satisfy the source Volterra equation and are not source counterexamples.'},indent=2))
