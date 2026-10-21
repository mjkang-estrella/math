"""Bounded arithmetic diagnostics; not a theorem verifier."""
import json, math
from pathlib import Path

def prime(n):
 return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
def leg(n,p):
 v=pow(n%p,(p-1)//2,p)
 return -1 if v==p-1 else v
out=[]
for B in [2,5,10,20]:
 used=[]; obligations=[]
 for n in range(1,B+1):
  if n%3==0 and math.isqrt(n//3)**2==n//3:continue
  p=next(p for p in range(max(B+1,5),10000) if prime(p) and p%3==1 and p not in used and leg(-n,p)==-1)
  used.append(p);obligations.append((n,p,'a'))
 q=next(q for q in range(max([B]+used)+1,20000) if prime(q) and q%12==5)
 P=math.prod(used)
 modulus=3*q*q
 residue=next(t for t in range(q*q) if P*t%(q*q)==q-1)
 residue=next(residue+j*q*q for j in range(3) if (residue+j*q*q)%3==1)
 ell=next(residue+k*modulus for k in range(100000) if residue+k*modulus>max([B,q]+used) and prime(residue+k*modulus) and residue+k*modulus not in used)
 a=P*ell
 for n in range(1,B+1):
  if n%3==0 and math.isqrt(n//3)**2==n//3:obligations.append((n,q,'a+1'))
 for n,p,side in obligations:
  d=a if side=='a' else a+1
  assert d%p==0 and d%(p*p)!=0
  assert leg(-n if side=='a' else n,p)==-1
  # Enumerate the one-variable residual norm, not a bounded global search.
  possible={(-y*y)%p for y in range(p)} if side=='a' else {(x*x)%p for x in range(p)}
  assert n%p not in possible
 assert a%6==1 and math.isqrt(a*(a+1))**2!=a*(a+1)
 out.append(dict(B=B,P=P,q=q,ell=ell,a=a,determinant=4*a*(a+1),obstructions=sorted(obligations)))
p=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r136/notes/local-calculation.json');p.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([dict(B=x['B'],a=x['a'],obligations=len(x['obstructions'])) for x in out]))
