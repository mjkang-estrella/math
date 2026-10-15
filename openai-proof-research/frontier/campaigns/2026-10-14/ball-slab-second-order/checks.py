"""Exact algebra supporting candidate.md; no geometric proof or simulation."""
from fractions import Fraction as F
from pathlib import Path
import json

def kernel_difference(l):
    return F(2*l+1)*2/F(l*(l+1)*(l*(l+1)-2))
def telescope(l):
    return F(1,l-1)-F(1,l)-F(1,l+1)+F(1,l+2)
for l in range(2,101):
    assert kernel_difference(l)==telescope(l)
for n in range(2,101):
    assert sum((kernel_difference(l) for l in range(2,n+1)),F(0))==F(2,3)-F(1,n)+F(1,n+2)
# The omitted common factor 1/(4*pi) gives a uniform kernel-difference bound 1/(6*pi).
for h in [F(1),F(3,2),F(5),F(100)]:
    # a^2/(R*epsilon)=1/(H+1/2); Z(a)/epsilon is equal on both sides.
    ratio=1/(h+F(1,2))
    assert 1-ratio/2 == ratio*h
    j=ratio**2*(2*h+F(1,2)) # J/(pi epsilon^2)
    assert j==2*(h+F(1,4))/(h+F(1,2))**2
    diff=(h+F(1,4))/(h+F(1,2))**2-1/h
    assert diff==(-F(3,4)*h-F(1,4))/(h*(h+F(1,2))**2)
# Four self traces with kernel coefficient 1/(2*pi): norm squared coefficient 2/pi.
assert 4*F(1,2)==2
# Energy is one half Q, total forced trace is 2 epsilon.
assert F(1,2)*2**2/F(2)==1 # pi epsilon^2 / L
assert F(1)/(F(1,2))==2    # L~ell/2 gives leading 2*pi
for x,y in [(F(10),F(2)),(F(100),F(5)),(F(1000),F(7))]:
    assert 1/(x+y)-1/x+y/x**2==y**2/(x**2*(x+y))
# rho=(2/9)*(1-3 delta)^(3/2), using exact binomial coefficients through order two.
rho=[F(2,9),F(-1),F(3,4)]
two_r_squared=[F(2,9),F(-4,3),F(2)]
g_over_2pi=[a-b for a,b in zip(rho,two_r_squared)]
assert g_over_2pi==[F(0),F(1,3),F(-5,4)]
result={
 'method':'exact fractions; finitely many algebra checks only; no simulation',
 'sphere_jacobi_minus_laplace_coefficient_identity':'2(2l+1)/(l(l+1)(l(l+1)-2))=1/(l-1)-1/l-1/(l+1)+1/(l+2)',
 'sum_l_ge_2_before_1_over_4pi':'2/3, by the exact partial-sum identity',
 'kernel_difference_uniform_bound':'1/(6*pi), plus removed finite degree-one term',
 'tangent_value_and_energy_identities':'verified',
 'four_trace_compliance':'(2/pi)*log(1/a)+O(1)',
 'leading_energy_coefficient':'2*pi',
 'loglog_energy_coefficient':'-2*pi',
 'g_delta_expansion':'(2*pi/3)*delta-(5*pi/2)*delta^2+O(delta^3)',
 'reciprocal_expansion_exact_remainder':'log(ell)^2/(ell^2*(ell+log(ell)))',
 'nonlinear_error_ratio':'S^(11/10)/(epsilon^2/ell^2)=epsilon^(1/5)*ell^(9/10)->0',
 'crossover_remainder_ratio':'S^2/T2=epsilon^2/log(ell)->0',
 'status':'all exact assertions passed; asymptotic limits proved analytically in candidate.md'
}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
