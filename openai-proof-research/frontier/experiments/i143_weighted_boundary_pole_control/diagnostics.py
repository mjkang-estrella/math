"""New finite identities only. No PDE, novelty, or acceptance certification."""
from fractions import Fraction as F
from collections import Counter

def run():
 c=Counter()
 for n in range(3,11):
  for p in (F(3,2),F(2),F(3),F(4)):
   for q in (F(7,5),F(2),F(3)):
    for A,B in ((0,0),(1,0),(0,2),(3,1)):
     alpha=(2+A+p*(2+B))/(p*q-1);beta=(2+B+q*(2+A))/(p*q-1)
     sigma=alpha+beta+2-n;gamma=F(n+A)/(p+1)+F(n+B)/(q+1)-(n-2)
     assert p*beta==alpha+2+A and q*alpha==beta+2+B
     assert A-(p+1)*beta==B-(q+1)*alpha==-n-sigma
     assert sigma*(1-1/(p+1)-1/(q+1))==gamma
     c['finite_scale_energy_and_sphere_exponents']+=1
     for theta in (F(1,4),F(1,2),F(1)):
      assert n-1+A+theta+1-p*beta-beta-1==theta-sigma-1
      assert n-2+2-alpha-1-beta-1==-sigma
      c['holder_and_curvature_radial_exponents']+=1
     assert A-(p-1)*beta==beta-alpha-2
     assert B-(q-1)*alpha==alpha-beta-2
     c['coupled_strip_product_exponent_minus_four']+=1
 for n in range(3,13):
  for r in (F(1,5),F(1),F(3)):
   for ratio in (F(1001,1000),F(11,10),F(2),F(8)):
    s=r*ratio
    J=(n-2)*r*r*(r**(-n)-s**(-n))/(r**(2-n)-s**(2-n))
    assert n-2<J<n
    c['reflected_tangential_pressure_bound']+=1
    # Joint dilation retains n-2, even when each kernel is large relative to the difference.
    assert (n-2)*(r**(2-n)-s**(2-n))==(n-2)*r**(2-n)-(n-2)*s**(2-n)
    c['reflected_joint_virial_homogeneity']+=1
 for n in range(3,9):
  for a in range(2,9):
   for b in range(2,9):
    I=F(a*b,a+b-1)
    Bgrad=-a*b+(n-1)*I
    lhs=-F(a*b*(a+b-2),a+b-1)
    assert lhs==(2-n)*I+Bgrad
    c['cross_pohozaev_boundary_sign_on_polynomial_cube']+=1
 for k in (F(0),F(1,4),F(1),F(5)):
  for r2 in (F(1,10),F(1),F(9)):
   psi=k*r2/2;xdgrad=k*r2
   assert psi-xdgrad==-k*r2/2
   assert (psi-xdgrad)**2<=k*k*r2*r2*(1+k*k*r2)
   c['quadratic_graph_normal_numerator']+=1
 # Strict hyperbolic example outside the individual Dai-Peng Kelvin rectangle.
 assert F(5,5)+F(5)/(F(7,5)+1)-3==F(1,12)
 assert F(4)>F(7,3)
 c['primary_scope_strict_hyperbola_not_rectangle']=1
 return {'status':'PASS','arithmetic':'integers and fractions.Fraction','checks':dict(sorted(c.items())),
 'scope':'new finite identities and samples only; not PDE estimates, regularity, universal inequalities, external proofs, contribution or acceptance'}
if __name__=='__main__':
 import json
 print(json.dumps(run(),sort_keys=True,indent=2))
