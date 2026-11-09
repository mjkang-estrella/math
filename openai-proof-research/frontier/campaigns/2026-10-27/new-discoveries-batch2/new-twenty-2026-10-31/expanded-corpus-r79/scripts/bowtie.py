from fractions import Fraction as F
import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
# In intended model, the positive tensor root z satisfies z^3>t+1 and phi(z)=1; phi is increasing there.
for t in range(8,257):
 def phi(z):return (z**3-t)**2*(1-F((t+1)**2,1)/z**6)
 lo=F(0);hi=F(t+2)
 # compare polynomial phi-1 only after cubic threshold; below threshold lies below root.
 for _ in range(64):
  z=(lo+hi)/2
  if z**3<=t+1 or phi(z)<1:lo=z
  else:hi=z
 # alpha/beta = z^2-t/z increasing; upper endpoint strictly<1 proves actual<1.
 beta_top=hi**3-hi<t
 # At lambda threshold L, positive quotient-vector residual is (3L+2t)/(L^2-t-1)>0.
 # Quadratic isolator and exact rational denominator bound checked.
 a,b=F(t+2),F(t+4)
 for _ in range(64):
  z=(a+b)/2
  if z*z-(t+2)*z-2*t<0:a=z
  else:b=z
 out.append({'t':t,'tensor_z_bracket':[str(lo),str(hi)],'beta_gt_alpha_certified_in_quotient':beta_top,'shadow_L_bracket':[str(a),str(b)],'shadow_residual_positive':a*a>t+1 and 3*a+2*t>0})
(D/'outputs/search-353438.json').write_text(json.dumps({'scope':'intended five-coordinate tensor/shadow model, all integer t8..256; rational bisection64steps, exact Fraction comparisons. This is quotient-model search, not certification of the inconsistent displayed source edge-set.','cases':out},indent=2)+'\n')
