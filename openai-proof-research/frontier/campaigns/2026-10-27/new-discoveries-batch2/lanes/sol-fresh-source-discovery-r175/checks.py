import json,hashlib
from fractions import Fraction as Q
from pathlib import Path
L=Path(__file__).resolve().parent
A=2**26;c=Q(1,2*(A+1));P=8*A
# e^2 > 5 from the positive exponential series, e^8 > 625.
tail=2*Q(1,5)/(1-Q(1,625))
assert tail<Q(1,2)
# log((A+2)/2) > 25 log 2 > 50/3.
ratio=Q(50,3)*(A+1)/(16*A)
assert ratio>Q(25,24)>1
v=(Q(A**3,3)+A*A+2*A+2)/(A+1)
assert 2*c*(A+1)==1 and v>0
# Closed central-strip formula, independent of the coarse analytic bound:
# p(r)/c=A-r+1+exp(-3A)(exp(r)-exp(-r))/(1+exp(-4A)).
# At r=A: p/c=(1+q^2)/(1+q^4), d_mu p/c=(1-q^2)/(1+q^4).
periodic=0
for den in range(5,40):
 q=Q(1,den)
 assert 1+(q*q-q**4)/(1+q**4)==(1+q*q)/(1+q**4)
 assert 1-(q*q+q**4)/(1+q**4)==(1-q*q)/(1+q**4)
 assert (1-q*q)/(1+q**4)>Q(1,2)
 periodic+=1
# Elementary quadratic product comparison used in the full routine bridge.
n=0
for x in range(1,10):
 for y in range(1,10):
  for u in range(1,10):
   for w in range(1,10):
    if x+y<u+w and x*y<u*w:
     for t in [Q(1,10),Q(1),Q(10)]:
      assert (1+t*x)*(1+t*y)<(1+t*u)*(1+t*w);n+=1
for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
 if 'sha256' in r:assert hashlib.sha256((L/'sources'/r['name']).read_bytes()).hexdigest()==r['sha256']
out=dict(status='PASS',A=A,tail_bound=str(tail),information_ratio_lower_bound=str(ratio),variance=str(v),quadratic_controls=n,periodic_tail_controls=periodic,scope='Exact rational supporting controls; no estimation theorem, source falsifier, or finite-to-uniform extrapolation.')
print(json.dumps(out,indent=2))
