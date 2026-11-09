"""Exact bounded diagnostics; run only under the assigned helper_guard.py."""
from pathlib import Path
import json,itertools,math
R=Path(__file__).resolve().parent
def prime(n):
 return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
def firstfactor(n):
 for d in range(2,math.isqrt(n)+1):
  if n%d==0:return d
 return n
cases=[]
for k in range(1,13):
 for E in [[],[2],[2,3,5]]:
  q=next(q for q in [3,5,7,11,13] if k%q)
  N=q*math.prod(E);S=sum(N**j for j in range(q));p=firstfactor(S)
  assert prime(p) and p not in E and p!=q and (p-1)%q==0
  # N itself supplies the element of order q: no cyclicity theorem needed.
  z=N%p;assert z!=1 and pow(z,q,p)==1
  for c in [1,2,3,-1]:
   if c%p==0:continue
   u,v=1,z
   for t in range(12):
    assert u and v and u!=v
    assert v*pow(u,-1,p)%p==pow(z,k**t,p)
    u,v=c*pow(u,k,p)%p,c*pow(v,k,p)%p
  cases.append(dict(k=k,E=E,q=q,N=N,p=p))
# Complete small diagnostic coefficient box, not a proof of classification.
mons=[(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]
survivors=[]
for coeff in itertools.product([-1,0,1],repeat=6):
 if all((sum(c*pow(x,i,p)*pow(y,j,p) for c,(i,j) in zip(coeff,mons))%p==0)==(x==0)
        for p in [2,3,5,7] for x in range(p) for y in range(p)):
  survivors.append(coeff)
assert len(survivors)==4
assert all(sum(c!=0 for c in cs)==1 and (cs[1] or cs[3]) for cs in survivors)
# A single prime does NOT imply a polynomial identity: x+y^2-y over F_2.
assert all(((x+y*y-y)%2==0)==(x==0) for x in range(2) for y in range(2))
out=dict(status='PASS: diagnostics only',cyclotomic_ratio_cases=cases,small_box_survivors=survivors,single_prime_nonmonomial=True)
(R/'checker-evidence.json').write_text(json.dumps(out,indent=2));print('PASS',len(cases),'prime constructions;',len(survivors),'small-box survivors')
