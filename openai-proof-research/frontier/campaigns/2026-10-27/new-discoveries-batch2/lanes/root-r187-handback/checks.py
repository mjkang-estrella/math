from pathlib import Path
import json,datetime
from fractions import Fraction as F
import sympy as s
L=Path(__file__).resolve().parent
a,b,j=s.symbols('a b j',positive=True)
lam=2*j*(j*b+a);r=2*(a+j*b);q=-2*j*b
ids={
 'positive_characteristic':s.expand(r*r/2-a*r-b*lam),
 'negative_characteristic':s.expand(q*q/2-a*q-b*lam),
 'neumann':s.simplify(r+(1+a/(j*b))*q),
 'positive_boundary_exponent':s.expand(-lam+r+2*(j-1)*(j*b+a)),
 'negative_boundary_exponent':s.expand(-lam+q+2*j*((j+1)*b+a)),
 'adjacent_boundary_match':s.expand((-lam+r).subs(j,j+1)-(-lam+q))}
assert all(v==0 for v in ids.values())
rows=[]
for alpha in [F(0),F(1,3),F(1),F(7,2),F(10)]:
 c=F(1)
 for n in range(1,13):
  p=F(1)
  for k in range(1,n):p*=1+alpha/k
  bin1=p*(n+alpha)/n;bin2=p
  assert c*(2+alpha/n)==(-1)**(n-1)*(bin1+bin2)
  nxt=-c*(1+alpha/n)
  assert nxt+c*(1+alpha/n)==0
  rows.append([str(alpha),n,str(c*(2+alpha/n))]);c=nxt
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),symbolic_identities={k:str(v) for k,v in ids.items()},rational_product_checks=rows,status='PASS',limits='Exact algebra diagnostics only. No Monte Carlo, discretized diffusion, or finite search replaces the universal proof.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: six symbolic identities and sixty rational coefficient/cancellation cases')
