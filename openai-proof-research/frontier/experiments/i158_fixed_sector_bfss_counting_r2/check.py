"""New finite diagnostic only. Never a universal proof or completed-review certificate."""
from fractions import Fraction as F
import math,itertools

def checks():
 cases=0
 for x,y in [(F(3),F(2)),(F(7,3),F(1,5)),(F(101,100),F(1)),(F(20),F(1,10))]:
  a=x*x+y*y;b=-2*x*y;det=a*a-b*b
  assert det==(x*x-y*y)**2
  inv=[[a/det,-b/det],[-b/det,a/det]]
  pp=1/(2*(x-y)**2);mm=1/(2*(x+y)**2)
  assert inv==[[pp+mm,pp-mm],[pp-mm,pp+mm]]
  cases+=1
 w=[(F(1,2),)+tuple(F(s,2) for s in ss) for ss in itertools.product([-1,1],repeat=3)]
 assert len(w)==8
 assert [3*sum(v[j]/2 for v in w) for j in range(4)]==[6,0,0,0]
 assert F(3072+9,3)-1024==3 and 3080>3072+6
 assert 384**2*6<1024**2 and 13*12==156
 g=math.gamma(0.25)
 phase=(2*math.pi)**-3*(4*math.pi/3)*2**1.5*g**3*math.gamma(2.5)/(96*math.gamma(3.25))
 claimed=math.sqrt(2)*g*g/(270*math.pi**1.5)
 assert math.isclose(phase,claimed,rel_tol=3e-15)
 return dict(status='PASS',metric_instances=cases,fermionic_plane_weight_sum=[6,0,0,0],phase_prefactor=phase,scope='Finite arithmetic only; not representation classification, domain proof, weighted Poincare proof, Weyl theorem, completed reading, or contribution certification.')
