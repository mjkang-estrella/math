"""Finite exact identities only. No universal or asymptotic certification."""
from fractions import Fraction as F

def run():
 counts={'koebe_partial_fraction':0,'simple_boundary_poles':0,'radial_exponent_budget':0,'dyadic_shell_budget':0,'tail_coefficients':0}
 # Real rational evaluation points are finite diagnostics of exact displayed identities.
 for den in range(2,23):
  for num in range(-den+1,den):
   z=F(num,den)
   assert (1-z)**3/(1+z)==-z*z+4*z-7+8/(1+z)
   counts['koebe_partial_fraction']+=1
   assert 1/(1-z*z)==F(1,2)/(1-z)+F(1,2)/(1+z)
   assert 1/(1-z)==-1/(z-1)
   counts['simple_boundary_poles']+=2
 for j in range(2,129):
  u=2-F(1,j);q=u/2;epsilon=(1-q)/(2*q)
  assert q*(1+epsilon)==(1+q)/2<1
  assert u+F(1,j)==2
  counts['radial_exponent_budget']+=1
  C=F(j,7);level=F(j+2,3)
  assert (2*level)**2*(C/level**2)==4*C
  counts['dyadic_shell_budget']+=1
 for c in [F(8),F(1),F(1,2),F(3,7)]:
  disk=c*c/2;image=c*c/4
  assert disk==2*image
  counts['tail_coefficients']+=1
 assert F(8)**2/2==32 and F(8)**2/4==16
 assert F(1,2)**2+F(1,2)**2==F(1,2)
 return dict(status='PASS',counts=counts,scope='Finite rational identities only; no universal analytic proof, endpoint estimate, asymptotic or substantiality certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
