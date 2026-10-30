"""Independent exact algebra diagnostics; does not certify stochastic analysis."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json, datetime
import sympy as s

p = Path(__file__).resolve().parent
j, a, b = s.symbols('j a b', positive=True)
lam = 2*j*(j*b+a)
r, z = 2*(a+j*b), -2*j*b
v = 1+a/(j*b)
identities = {
    'positive_characteristic': r*r/2-a*r-b*lam,
    'negative_characteristic': z*z/2-a*z-b*lam,
    'Neumann_pair': r+v*z,
    'first_boundary_exponent': -lam+r+2*(j-1)*(j*b+a),
    'second_boundary_exponent': -lam+z+2*j*((j+1)*b+a),
    'next_boundary_cancellation': (-lam+z)-(-lam+r).subs(j,j+1),
    'seed_constant_boundary': (-lam+r).subs(j,1),
    'positive_exponent_quadratic_majorant':
        2*(j-1)*(j*b+a)-b*j*j-(b*j*(j-2)+2*a*(j-1)),
    'root_step_forces_next_lambda':
        (r+2*b)**2/2-a*(r+2*b)-b*lam.subs(j,j+1),
}
out={k:str(s.factor(x)) for k,x in identities.items()}
assert all(x=='0' for x in out.values())
records=[]
for alpha in map(F, ['0','1/7','1/2','3/2','10']):
    coeff=F(1); terms={}; detail=[]
    for n in range(1,26):
        w=1+alpha/n
        def choose(x,k):
            t=F(1)
            for q in range(k):t*=x-q
            return t/factorial(k)
        literal=(-1)**(n-1)*(choose(n+alpha,n)+choose(n+alpha-1,n-1))
        assert literal==coeff*(1+w)
        # b=1 after exact scaling: exponent polynomial in h has rational coefficient.
        e1=2*(n-1)*(n+alpha);e2=2*n*(n+1+alpha)
        terms[e1]=terms.get(e1,F(0))+coeff
        terms[e2]=terms.get(e2,F(0))+coeff*w
        nz={e:c for e,c in terms.items() if c}
        assert nz=={F(0):F(1),e2:coeff*w}
        detail.append({'N':n,'boundary_residual_exponent':str(e2),
                       'boundary_residual_coefficient':str(coeff*w)})
        coeff=-coeff*w
    records.append({'alpha':str(alpha),'finite_truncations':detail})
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status':'PASS','symbolic_identities':out,'exact_coefficient_and_telescoping_cases':125,
        'records':records,'limit':'Exact algebra diagnostics only; convergence, Ito, terminal limits and eligibility assessed in review.md.'}
(p/'checker-evidence.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'}))
