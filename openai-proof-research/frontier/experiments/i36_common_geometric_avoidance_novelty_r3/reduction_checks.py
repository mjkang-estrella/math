"""Exact checks of the two input substitutions used in the significance reduction.
These are diagnostics of formulas, not a proof or a test of significance.
"""
from fractions import Fraction as F
import json

def run():
 rec=0;meshes=0
 for M in range(2,9):
  for r0 in (1,3,11):
   for g in (1,5,19):
    sigma=M*r0+(M-1)*g
    for h in range(1,10):
     if h>1:
      r=max(r0,g+sigma);assert r==g+sigma
      sigma=M*(r+g+sigma)+(M-1)*g
     P=M*(2*M)**(h-1)
     Q=(M-1)*(2*M)**(h-1)+(3*M-1)*((2*M)**(h-1)-1)//(2*M-1)
     assert sigma==P*r0+Q*g;rec+=1
 # In log_2 coordinates, a <= n*u-v <= b. Exact integer mesh count.
 for u in (F(1,7),F(1,2),F(1),F(5,3),F(3)):
  for v in (F(0),F(1,5),F(1,2),F(1)):
   for a in (3,7,19):
    for r in (1,2,9,31):
     lo=(a+v)/u;hi=(a+r+v)/u
     ceil=lambda z:-((-z.numerator)//z.denominator)
     floor=lambda z:z.numerator//z.denominator
     actual=[n for n in range(1,floor(hi)+2) if a<=n*u-v<=a+r]
     assert len(actual)==max(0,floor(hi)-ceil(lo)+1)
     assert len(actual)>=F(r)/u-1
     if r>=2*u:assert len(actual)>=F(r)/(2*u)
     meshes+=1
 return {'status':'PASS','affine_span_identity_cases':rec,'physical_window_integer_mesh_cases':meshes,'span_formula':'sigma_h = M(2M)^(h-1) r0 + [(M-1)(2M)^(h-1)+(3M-1)((2M)^(h-1)-1)/(2M-1)]g','scope':'Exact supporting diagnostics of an algebraic compatibility reduction. No claim of proof certification or novelty certification.'}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
