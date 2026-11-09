"""Exact integer gcd screening of Levens 2511.03082v1 Definition Sect3.
P_n = sum_{j=0}^n binom(n,floor(j/2)) z^j.
Finite data only; no inference of universal coprimality.
"""
import sys, math, json, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / '.pydeps'))
from flint import fmpz_poly
N=int(sys.argv[1]) if len(sys.argv)>1 else 200
start=time.time(); polys=[fmpz_poly([math.comb(n,j//2) for j in range(n+1)]) for n in range(N+1)]
nontriv=[]; checked=0
for n in range(1,N+1):
 for m in range(n):
  g=polys[n].gcd(polys[m]); checked+=1
  if g.degree() > (1 if n%2 and m%2 else 0): nontriv.append({'n':n,'m':m,'gcd':str(g)})
 if n%25==0: print(json.dumps({'through':n,'pairs':checked,'nontrivial':nontriv,'seconds':time.time()-start}),flush=True)
print(json.dumps({'N':N,'pairs':checked,'nontrivial':nontriv,'seconds':time.time()-start}),flush=True)
