"""Bounded exact-arithmetic diagnostics; not mathematical acceptance gates."""
from fractions import Fraction as F
from math import factorial,comb
from pathlib import Path
import json
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132')
K=F(961,400);D=2*K/3;p=K/2;l=p+D;d=D/2;b=F(2,3)
J=l*l*F(61,64)-F(685,256)
I=l*l*(F(685,256)-F(61,64))-F(11101,1024)+F(685,256)
rows={'K':K,'threshold':64*K,'J':J,'I':I,'g_bound':F(600,157)*F(81,100)*(F(16,105)+F(625,118881)),
'four_margin':64*K/(6*K**4)*I-p*(l*l-p*p)/2,
 'three_margin':d**4-d*d/4-F(1,4),
 'two_constant':(D-b)*b**3+(3*D*b-6*b*b)/3-F(1,3),
 'two_coefficient':(D-b)*b*b+(D-3*b)/3,
 'hypersurface_margin':64*K-F(4096,27)}
assert all(x>0 for x in rows.values()) and rows['g_bound']<F(1,2)
checks=[]
for n in (3,5,7):
 N=n-1
 for c,x in [(F(3,2),F(1,2)),(F(5,2),F(1,2)),(F(3),F(3,4)),(F(2),F(1))]:
  L=max(F(0),(c*x-1)/(c-1))
  integral=F(factorial(n),factorial(N-1))*((x-1/c)*L**N/N-(1-1/c)*L**(N+1)/(N+1))
  formula=max(F(0),c*x-1)**n/(c*(c-1)**N)
  assert integral==formula
  finite=[]
  for k in (80,160):
   cutoff=k*x; count=0
   for a in range(int(cutoff)+1):
    for T in range(int(cutoff)+1-a):
     if a+T<cutoff and c*a+T>=k:count+=comb(T+N-1,N-1)
   finite.append({'k':k,'normalized_count':str(F(factorial(n)*count,k**n))})
  checks.append({'n':n,'c':str(c),'x':str(x),'leading_loss':str(formula),'finite_counts':finite})
out={'purpose':'Exact scalar/profile arithmetic and finite lattice diagnostics only; no correctness or contribution gate.', 'profile':{k:str(v) for k,v in rows.items()},'triangular_integral_checks':checks}
(R/'artifacts/exact-calculations.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact profile margins positive; 12 integral identities checked; 24 bounded finite counts retained.')
