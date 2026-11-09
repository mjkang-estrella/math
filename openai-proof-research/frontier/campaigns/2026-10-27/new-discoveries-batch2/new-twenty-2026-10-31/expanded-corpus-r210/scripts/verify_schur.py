from pathlib import Path
from fractions import Fraction
from math import factorial,prod
from collections import Counter
L=Path(__file__).resolve().parents[1];exec(compile((L/'scripts/search_schur.py').read_text().split('\nfor n in range')[0],str(L/'scripts/search_schur.py'),'exec'))
for n in range(1,10):
 ps=parts(n);z={rho:prod(k**m*factorial(m) for k,m in Counter(rho).items()) for rho in ps}
 for i,lam in enumerate(ps):
  dimension=factorial(n)//prod(lam[r]-c+sum(v>c for v in lam[r+1:]) for r in range(len(lam)) for c in range(lam[r]))
  assert chi(lam,(1,)*n)==dimension
  for j,mu in enumerate(ps[:i+1]):assert sum(Fraction(chi(lam,rho)*chi(mu,rho),z[rho]) for rho in ps)==(i==j)
 print('dimension and character row orthogonality PASS n='+str(n),flush=True)
