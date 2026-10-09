from pathlib import Path
from fractions import Fraction as F
import itertools, math, json
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/experiments/i20_pde_kinetic_discovery/diagnostics.json'
count=0
for n in range(1,6):
 edges=list(itertools.combinations(range(n),2))
 a=[F(i+1,7) for i in range(n)];b=[F(n-i,11) for i in range(n)]
 for mask in range(1<<len(edges)):
  ee=[e for j,e in enumerate(edges) if mask>>j&1]
  sets=[s for s in range(1<<n) if all(not(s>>i&1 and s>>j&1) for i,j in ee)]
  weight=lambda w,s:math.prod(w[i] for i in range(n) if s>>i&1)
  wa={s:weight(a,s) for s in sets};wab={s:weight([x+y for x,y in zip(a,b)],s) for s in sets}
  za=sum(wa.values());zab=sum(wab.values());p0=za/zab
  tv=sum(abs(wa[s]/za-wab[s]/zab) for s in sets)/2
  assert tv<=1-p0
  assert zab<=za*math.prod(1+x for x in b)
  for t in [F(0),F(1,3),F(2,3),F(1)]:
   w=[x+t*y for x,y in zip(a,b)];z=sum(weight(w,s) for s in sets)
   deriv=sum(sum(b[i]*math.prod(w[j] for j in range(n) if s>>j&1 and j!=i) for i in range(n) if s>>i&1) for s in sets)
   q=max(sum(a[j]+b[j] for j in range(n) if j==i or (min(i,j),max(i,j)) in ee) for i in range(n))
   assert sum(b)*max(F(0),1-q)<=deriv/z<=sum(b)
  count+=1
# Ball lens, union and contact-excess coefficients in units of pi.
lens=2*(F(1)-F(1,3)-F(1,2)+F(1,24))
ball=F(4,3);union=2*ball-lens
assert lens==F(5,12) and union==F(9,4) and 2*ball-union==F(5,12)
poisson=[]
for lam in [F(1,4),F(1),F(4)]:
 for n in [16,64,256,1024]:
  # Independent exclusion cells: q=lam/n, exact partition ratio.
  p0=float((1+lam/n)**(-n));target=math.exp(-float(lam))
  poisson.append({'lambda':float(lam),'cells':n,'p_zero':p0,'poisson_p_zero':target})
out={'status':'PASS','finite_graph_cases':count,'rational_partition_and_TV_checks':True,'lens_over_pi':str(lens),'union_over_pi':str(union),'contact_correction_over_pi':str(2*ball-union),'finite_poisson_diagnostics':poisson,'limitation':'Finite checks supplement the written continuum arguments. No particle simulation, analytic convergence proof, or proof/significance review is claimed.'}
OUT.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='finite_poisson_diagnostics'},indent=2))
