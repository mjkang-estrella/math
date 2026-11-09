# Exact Kronecker coefficients g(lam,lam,mu) for symmetric lam |- n via Murnaghan-Nakayama.
import sys,json
from fractions import Fraction
from functools import lru_cache
from math import factorial
from collections import Counter
def parts(n,m=None):
  if m is None:m=n
  if n==0: yield (); return
  for k in range(min(n,m),0,-1):
    for p in parts(n-k,k): yield (k,)+p
def conj(l): return tuple(sum(1 for x in l if x>i) for i in range(l[0])) if l else ()
@lru_cache(None)
def chi(lam,rho):
  # rho: tuple of cycle lengths; remove border strips of size rho[0] via beta-numbers
  if not rho: return 1 if sum(lam)==0 else 0
  r=rho[0]; rest=rho[1:]
  L=len(lam); beta=[lam[i]+L-1-i for i in range(L)]; s=set(beta); tot=0
  for b in beta:
    if b-r>=0 and (b-r) not in s:
      sign=(-1)**sum(1 for c in beta if b-r<c<b)
      nb=sorted([c for c in beta if c!=b]+[b-r],reverse=True)
      nl=tuple(x for x in (nb[i]-(L-1-i) for i in range(L)) if x>0)
      tot+=sign*chi(nl,rest)
  return tot
def z(rho):
  c=Counter(rho); out=1
  for k,m in c.items(): out*=k**m*factorial(m)
  return out
n=int(sys.argv[1]); P=list(parts(n)); res={}
sym=[l for l in P if conj(l)==l]
for lam in sym:
  zero=[]
  for mu in P:
    g=sum(Fraction(chi(lam,r)**2*chi(mu,r),z(r)) for r in P)
    assert g.denominator==1 and g>=0
    if g==0: zero.append(mu)
  res[str(lam)]=[str(m) for m in zero]
ok=[k for k,v in res.items() if not v]
print(json.dumps(dict(n=n,symmetric=[str(s) for s in sym],missing_constituents=res,works=ok)))
