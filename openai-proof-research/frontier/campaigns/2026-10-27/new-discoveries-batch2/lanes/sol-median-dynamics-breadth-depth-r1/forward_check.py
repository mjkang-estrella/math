"""Independent forward mass propagation; compares every certified coefficient."""
from pathlib import Path
import json
from fractions import Fraction
from math import factorial
L=Path(__file__).resolve().parent
c=json.loads((L/'certificate-results.json').read_text());N=2**c['n'];edges=c['edges']
dist=[2**bin(s).count('1')*3**(10-bin(s).count('1')) for s in range(N)]
S=Fraction(0)
for k in range(241):
 new=[0]*N
 for s in range(N):
  for v in range(10):
   nei=[a+b-v for a,b in edges if a==v or b==v]
   vote=sum(1 if s&(1<<j) else -1 for j in nei)
   dest=s|(1<<v) if vote>0 else s&~(1<<v) if vote<0 else s
   new[dest]+=dist[s]
 current=sum(x for s,x in enumerate(dist) if s&2)
 following=sum(x for s,x in enumerate(new) if s&2)
 coefficient=following-10*current
 assert coefficient==int(c['coefficients'][k]),k
 assert sum(dist)==5**10*10**k
 S+=Fraction(8**k,factorial(k))*coefficient
 dist=new
assert S==Fraction(int(c['S']['numerator']),int(c['S']['denominator']))
(L/'forward-results.json').write_text(json.dumps(dict(passed=True,coefficients_checked=241,states=1024,all_clock_choices_per_state=10,total_mass_checked=True),indent=2))
print('PASS: independent forward propagation agrees in all 241 integer coefficients.')
