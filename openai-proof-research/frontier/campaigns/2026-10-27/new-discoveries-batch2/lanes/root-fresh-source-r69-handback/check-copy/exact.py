from fractions import Fraction as F
import json,math
import sympy as s
x,t,y,a,b=s.symbols('x t y a b',positive=True)
r=s.Function('r')(x)
# chain rule: (log r(sqrt t))'' at t=x²
L=s.log(r)
assert s.simplify((x*s.diff(L,x,2)-s.diff(L,x))/(4*x**3)-(x*(r*s.diff(r,x,2)-s.diff(r,x)**2)-r*s.diff(r,x))/(4*x**3*r**2))==0
# Gaussian folded-integrand Taylor in the squared argument, no sqrt expansions needed
K=sum((2*a*y)**(2*j)*t**j/s.factorial(2*j) for j in range(4))*s.exp(-a*t)
A=s.simplify(s.diff(K,t).subs(t,0));B=s.simplify(s.diff(K,t,2).subs(t,0)-A**2)
assert s.expand(A-(-a+2*a*a*y*y))==0
assert s.expand(B+F(8,3)*a**4*y**4)==0
checks=[]
for ai in range(1,9):
 for bi in range(1,9):
  aa=F(ai,3);bb=F(bi,5);c=aa+bb
  ey2=1/(2*c);ey4=3/(4*c*c)
  EB=-F(8,3)*aa**4*ey4;VA=4*aa**4*(ey4-ey2**2)
  assert EB<0 and VA>0 and EB+VA==0
  checks.append({'a':str(aa),'b':str(bb),'mean_log_curvature':str(EB),'score_variance':str(VA)})
# Verify heat-flow differentiation formula for v=g_ss, not a PDE positivity proof.
z=s.symbols('z');g=s.Function('g')(z);v=s.diff(g,z,2)
heat=2*s.diff(g,z)+4*z*(s.diff(g,z,2)+s.diff(g,z)**2)
assert s.simplify(s.diff(heat,z,2)-(4*z*s.diff(v,z,2)+(10+8*z*s.diff(g,z))*s.diff(v,z)+16*s.diff(g,z)*v+8*z*v*v))==0
# normalization-independent curvature chain rule tested on arbitrary polynomial r
for coeff in [(1,2,3),(2,-1,4),(3,0,2)]:
 rr=sum(c*x**(2*j) for j,c in enumerate(coeff));hh=s.log(sum(c*t**j for j,c in enumerate(coeff)))
 assert s.simplify(s.diff(hh,t,2).subs(t,x*x)-(x*(rr*s.diff(rr,x,2)-s.diff(rr,x)**2)-rr*s.diff(rr,x))/(4*x**3*rr**2))==0
out={'gaussian_cancellation_exact':checks,'symbolic_identities':7,'source_proof':False}
open('exact.json','w').write(json.dumps(out,indent=2));print('PASS 64 exact cancellations; symbolic score, heat, chain-rule identities')
