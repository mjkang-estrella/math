"""Exact auxiliary route checks. NOT a resolution of Conjecture 2."""
from fractions import Fraction as Q
import json
from pathlib import Path

def norm_data(r,a):
 # p=(z-r)(z+a); |p|²=A+B*x-C*x², x=Re z.
 A=(1+r*r)*(1+a*a); B=2*(a*(1+r*r)-r*(1+a*a)); C=4*r*a
 x=B/(2*C); assert -1<x<1
 M2=A+B*B/(4*C)
 D=2+abs(a-r) # derivative=2z+(a-r); triangle bound attained
 return {'vertex':x,'norm_squared':M2,'derivative_norm':D,'ratio_squared':D*D/M2}
u=norm_data(Q(3),Q(3));v=norm_data(Q(4),Q(3))
assert u['norm_squared']==100 and u['ratio_squared']==Q(1,25)
assert v['vertex']==Q(11,48) and v['norm_squared']==Q(8281,48)
assert v['ratio_squared']==Q(432,8281)>u['ratio_squared']
assert max(u['ratio_squared'],v['ratio_squared'])<1
# Polynomial numerator in the single-active-point variational equation:
# (z-w)*(z-a)*L+(w-a) = [(z-w)*z*L+w] - a*[(z-w)*L+1].
# A linear polynomial with two distinct roots must have both coefficients zero.
# Setting the a-coefficient to zero makes the constant coefficient w-z;
# this forces z=w, contradicting (z-w)*L+1=0.
# Check the substitution identity without symbolic or floating arithmetic.
for z,w in [(Q(1),Q(-1)),(Q(2),Q(5))]:
 L=-1/(z-w)
 assert (z-w)*z*L+w == w-z !=0
out={'status':'PASS exact auxiliary checks; no full theorem endpoint',
 'radial_monotonicity_refuted':True,'p3':{k:str(x) for k,x in u.items()},
 'p4':{k:str(x) for k,x in v.items()},
 'variational_algebra':'linear numerator identity verified by expansion in discovery.md; sample substitutions checked here',
 'source_conjecture_refuted':False}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
