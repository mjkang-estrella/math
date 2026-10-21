"""Finite diagnostics of two displayed calculations; not mathematical gates."""
from pathlib import Path
from itertools import product
from math import comb
import json
ROOT=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r133')
checks=0
for d in range(1,6):
 for N in range(2,7):
  counts=[0]*(d*(N-1)+1)
  for v in product(range(N),repeat=d): counts[sum(v)]+=1
  for h in range(4):
   for k in range(1,d+3):
    r=h+(k-1)*N
    direct=sum(counts[:r+1])
    ie=sum((-1)**j*comb(d,j)*(comb(r-j*N+d,d) if r>=j*N else 0) for j in range(d+1))
    assert direct==ie
    if k>=d+1: assert direct==N**d
    checks+=1
out={'hilbert_count_cases':checks,'hilbert_status':'matched direct tuple counts; no genericity or theorem gate'}
try:
 import sympy as s
 z,Z,w,W=s.symbols('z Z w W')
 a,c,cp,cpp,e=s.symbols('a c cp cpp e', nonzero=True)
 variables=[z,w]; barred=[Z,W]; origin={z:0,Z:0,w:0,W:0}
 t=(w-W)/(2*s.I)-z*Z-e*z*z*Z*Z
 pot=-a*t+c*t**2/2+cp*t**3/6+cpp*t**4/24
 def deriv(*vs): return s.diff(pot,*vs).subs(origin)
 def curvature(i,j,k,l):
  return s.simplify(-deriv(variables[i],barred[j],variables[k],barred[l])+sum(inv*deriv(variables[i],variables[k],barred[q])*deriv(variables[q],barred[j],barred[l]) for q,inv in enumerate([1/a,4/c])))
 values={'horizontal':curvature(0,0,0,0),'mixed':curvature(0,0,1,1),'unbalanced':curvature(0,1,0,1)}
 expected={'horizontal':-4*a*e-2*c,'mixed':(cp+c*c/a)/4,'unbalanced':0}
 for k in values: assert s.simplify(values[k]-expected[k])==0
 out['curvature_jet']={k:str(v) for k,v in values.items()}
 out['curvature_scope']='one base coordinate fourth-order jet; consistency diagnostic, not full geometric proof'
except ImportError:
 out['curvature_scope']='sympy unavailable; no install attempted; handwritten derivation only'
(ROOT/'notes/math-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
