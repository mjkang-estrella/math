"""New finite rational diagnostics; no ancestor code, source theorem or novelty certification."""
from fractions import Fraction as F

def mul(a,b):
 out={}
 for i,x in a.items():
  for j,y in b.items():out[i+j]=out.get(i+j,F(0))+x*y
 return out
def diff(a):return {i-1:i*x for i,x in a.items() if i}
def integ(a):
 assert all(i>=0 for i in a)
 return sum(x*F(2**(i+1)-1,i+1) for i,x in a.items())
def shift(a,n):return {i+n:x for i,x in a.items()}
def run():
 # Radial unitary identity in R^27, on a compactly supported H^1 test.
 f={0:F(-2),1:F(3),2:F(-1)};u=shift(f,13)
 lhs=integ(shift(mul(diff(f),diff(f)),26))
 rhs=integ(mul(diff(u),diff(u)))+156*integ(shift(mul(u,u),-2))
 assert lhs==rhs
 # The 1/2 kinetic coefficient, not the coercive 1/4 coefficient,
 # sets the weight cost in the eigenfunction identity.
 assert F(1,2)*F(3,2)**2==F(9,8)
 c=F(2);a=F(1);b=c-F(9,8)*a*a;assert b>0
 for energy in range(1,8):
  r0=max(F(1),2*energy/b)
  for j in range(1,8):
   r=r0*j;assert b*r-energy>=b*r/2
 # Exact finite trial-space scaling j=n^3, R=n.
 for n in range(1,21):
  j=n**3;r=F(n);assert j*j/r**2+r**4+r+r**-2<=4*n**4
 assert F(27)+F(27,2)==F(81,2)
 assert 1/F(4,3)==F(3,4)
 assert F(3,4)+F(3,2)==F(9,4) # candidate phase-volume exponent only
 # Cosine/sine multiplier gradients at rational points of the unit circle.
 for p in range(-5,6):
  t=F(p,3);cs=(1-t*t)/(1+t*t);sn=2*t/(1+t*t)
  assert cs*cs+sn*sn==1
 return {'status':'PASS','radial_form_identity':1,'agmon_weight_budget':49,'radial_trial_scaling':20,'structure_factor_gradient_identity':11,'scope':'Finite arithmetic/form identities only. Not a universal proof, Weyl law, novelty or acceptance certificate.'}
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
