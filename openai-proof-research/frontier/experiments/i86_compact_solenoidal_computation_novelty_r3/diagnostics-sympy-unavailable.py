"""Independent finite algebra checks for the alternative significance reduction. No files written."""
import sympy as s, json
from fractions import Fraction as Q
r,t,A,B=s.symbols('r t A B', nonzero=True)
At=2/(A-B)+(B-3*A)/(3*t); Bt=1/(A-B)
def Dt(x):return s.diff(x,t)+s.diff(x,A)*At+s.diff(x,B)*Bt
P3=r*(r*r-B); P6=6*t*(r*r-A)-P3**2
compat=s.factor(s.diff(P6,r)+P3*Dt(P6)-2*Dt(P3)*P6)
gs=s.factor(s.diff(P3,r)+P3*Dt(P3)+Dt(P6)/2-P3/r+3*(A+t*At)-5*r*r)
assert compat==gs==0
# zeta representation implies precisely the two original CLV coefficient ODEs.
z,Z=s.symbols('z Z', nonzero=True); zp=-z/t+5*Z; Zp=z*Z**2/(3*t)-Z**3
alpha=(1/Z-z)/2; beta=(3/Z-z)/2
def deriv(f):return s.diff(f,z)*zp+s.diff(f,Z)*Zp
assert s.factor(deriv(alpha)-2/(alpha-beta)-(beta-3*alpha)/(3*t))==0
assert s.factor(deriv(beta)-1/(alpha-beta))==0
# Ordered two-rotation identity, relevant only to interpreting I80 mechanism.
z=s.symbols('z', positive=True);J=s.Matrix([[0,-1],[1,0]]);Rm=((1-z*z)*s.eye(2)-2*z*J)/(1+z*z)
assert s.simplify((s.eye(2)-Rm)*(s.eye(2)/2-J/(2*z)))==s.eye(2)
# Degree-two radial stress leaves quadrupole only; orthogonal axes kill it.
x,y,w=s.symbols('x y w');assert s.expand(sum(3*v*v-(x*x+y*y+w*w) for v in [x,y,w]))==0
rho=Q(1,100);assert rho*Q(44,3)<Q(1,2) and rho*22<1
support=Q(1,16)+Q(1,4096);assert support<Q(1,4)
# All finite checked source exponents; report contains general argument.
count=0
for k in range(65):
 for n in range(max(k,4),130):
  assert n+8-k>=8 and 2*n+19-k>=19
  assert n+7<=2**n
  count+=1
print(json.dumps({'status':'PASS_FINITE_DIAGNOSTICS_NOT_PROOF','CLV_compatibility':str(compat),'Grad_Shafranov_residual':str(gs),'coefficient_ODE_transform':'exact','Picard_radius':str(rho),'Picard_self_map_increment':str(rho*Q(44,3)),'Picard_contraction':str(rho*22),'moving_template_support_over_h':str(support),'two_rotation_inverse':'exact','orthogonal_quadrupole_sum':0,'exponent_cases':count},sort_keys=True,indent=2))
