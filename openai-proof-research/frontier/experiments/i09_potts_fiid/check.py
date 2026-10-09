"""Exact obstructions to two direct Potts factor-of-IID transfers."""
from fractions import Fraction as F
from itertools import product
import json

rows=[]
for q,a in [(3,F(2,5)),(4,F(3,8))]:
    lam=F(1,2)
    derivative=lam*a/((1-lam)/q+lam*a)
    assert derivative>lam
    rows.append({'q':q,'lambda':str(lam),'first_two_posterior_masses':str(a),
                 'cavity_derivative_eigenvalue':str(derivative),
                 'b_times_eigenvalue_squared_at_b4':str(4*derivative**2)})

for theta in [F(i,20) for i in range(21)]:
    transition={z:F(0) for z in product([-1,1],repeat=2)}
    for e in product([-1,1],repeat=3):
        p=F(1)
        for s in e:p*=(1+theta*s)/2
        transition[e[0]*e[2],e[1]*e[2]]+=p
    for z,p in transition.items():
        assert p==((1+3*theta**2)/4 if z==(1,1) else (1-theta**2)/4)
print(json.dumps({'derivative_examples':rows,'three_Ising_quotient_parameters_checked':21,
                  'all_exact_checks_pass':True,
                  'scope':'Local algebra only; no new Potts factor construction.'},indent=2))
