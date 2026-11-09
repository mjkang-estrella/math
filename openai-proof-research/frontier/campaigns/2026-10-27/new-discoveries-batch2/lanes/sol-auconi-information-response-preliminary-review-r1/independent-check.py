from fractions import Fraction as Q
from math import comb
import json
from pathlib import Path
# Polynomial integration over t in [0,1] against 2(1-t)dt.
def moment(n):
 return sum((Q(2*comb(n,k)*(-3)**k,(k+1)*(k+2)) for k in range(n+1)),Q(0))
M=[moment(n) for n in range(9)]
assert M[:5]==[1,0,Q(1,2),Q(-1,5),Q(3,5)]
a=Q(1,100);J=M[2]
# Score polynomial 1-3t; derivative in x is -3t(1-t).
Esprime=-3*(Q(2,2*3)-Q(2,3*4))
assert Esprime==-J
conditional_coefficient=a*J
response_numerator=conditional_coefficient**2*J
gamma=response_numerator/J
assert gamma==Q(1,40000)
r=4*a
assert r==Q(1,25) and 1-2*a==Q(49,50) and 1+4*a==Q(26,25)
Ez=[a**k*M[k]**2 for k in range(9)]
assert Ez[1]==0 and Ez[2]==a*a/4 and Ez[3]==a**3/25 and Ez[4]==9*a**4/25
quadratic=Ez[2]/2;cubic=-Ez[3]/6
remainder=Ez[4]/(12*(1-r))
upper=quadratic+cubic+remainder
gap=gamma-2*upper
assert remainder==Q(1,3200000000)
assert gap==Q(61,4800000000)>0
# Direct infinitesimal KL ratio coefficients.
cprime=-J;outputKL2=a*a*cprime*cprime*J/2;inputKL2=-Esprime/2
assert outputKL2/inputKL2==gamma
# Derive scalar entropy-series coefficient by multiplying log(1+z) by 1+z.
for k in range(2,30):
 assert Q((-1)**(k+1),k)+Q((-1)**k,k-1)==Q((-1)**k,k*(k-1))
# Honest reference moments, not numerical integration or finite sampling proof.
result=dict(status='PASS exact rational identities',moments=list(map(str,M[:5])),J=str(J),gamma=str(gamma),E_sprime=str(Esprime),entropy_cubic=str(cubic),remainder_bound=str(remainder),gamma_minus_2I_lower=str(gap),input_KL_h2=str(inputKL2),output_KL_h2=str(outputKL2),ratio=str(outputKL2/inputKL2),non_numeric_scope='Analytic all-real substitution, domination, uniform series and KL nonnegativity are proved in review.md, not inferred from this arithmetic checker.')
Path(__file__).with_name('checker-result.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
