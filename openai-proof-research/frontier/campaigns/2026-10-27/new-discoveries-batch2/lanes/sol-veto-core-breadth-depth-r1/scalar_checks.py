from fractions import Fraction as F
from pathlib import Path
import json
import sys
O=Path(__file__).resolve().parent
n=0
for u0 in range(13):
 for v0 in range(u0+1):
  u=F(u0,12);v=F(v0,12);T=1+u;S=T+v;mu=1/S
  for p0 in range(25):
   p=F(p0,24);floor=(p+v*(1-p))/S
   for j in range(13):
    q=floor+(1-floor)*F(j,12);K=mu*(1-p)+q
    if K>1:continue
    L=(T+1)*(K+mu*max(F(0),q+p-1))-(1+mu)
    assert L>=0
    if p<=T/(T+1):
     assert (T+1)*(mu*(1-p)+floor)-(1+mu)==v*(T-(T+1)*p)/S
    else:
     assert floor-1/(T+1)==(1-v)*((T+1)*p-T)/(S*(T+1))
     assert K+mu*(q+p-1)==(1+mu)*q
    n+=1
# Exact algebraic identity behind (8), evaluated on rational parameters, as a
# regression control; its symbolic derivation is explicitly in PROOF.md.
result={'pass':True,'exact_cases':n,'scope':'m=3 rational grid, certificate algebra only; proof is PROOF.md'}
if '--verify' in sys.argv:
 assert json.loads((O/'scalar-results.json').read_text())==result
else:
 (O/'scalar-results.json').write_text(json.dumps(result,indent=2))
print(n)
