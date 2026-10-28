"""Exact identities in the classical reduction; numerics are diagnostic only."""
from pathlib import Path
import hashlib
import json
import sympy as s

z, p, n = s.symbols('z p n', positive=True)
r = s.sqrt(1+z*z)
eta = r+s.log(z)-s.log(1+r)
a = 2+1/p
H = a*s.log(z)-eta/p
h = a*s.log(2)+s.log(p)+(1+1/p)*s.log(1+p)-2-1/p
out = {}
def check(name, expr):
    value = s.simplify(s.expand_log(expr, force=True))
    assert value == 0, (name, value)
    out[name] = True

check('eta_derivative', s.diff(eta,z)-r/z)
check('H_derivative', s.diff(H,z)-(a-r/p)/z)
check('saddle_square_identity', 1+4*p*(1+p)-(2*p+1)**2)
# At z*=2sqrt(p(1+p)), r=2p+1. Work in logs to avoid branch guessing.
logzstar = s.log(2)+(s.log(p)+s.log(1+p))/2
etastar = 2*p+1+logzstar-s.log(2*(p+1))
check('saddle_value', a*logzstar-etastar/p-h)
logw = s.log(1+z*z)/(4*p)-s.log(z)
logenvelope = s.log(z)+s.log(1+z*z)/(4*p)+s.log(1+r)/p-r/p
check('exact_global_envelope', logw+H-logenvelope)
headline = n*((1+1/(2*p))*s.log(n)-1-1/(2*p)
              +s.log(p)/2+(1+1/p)*s.log(1+p)/2)
check('headline_constant', a*(n/2)*s.log(n/2)+(n/2)*h-headline)
# Keep only order n terms in the source prefactor and Stirling.
loggamma_main = (n/2)*(s.log(n/2)-1)
prefactor_main = n*s.log(s.pi)-n*s.log(2)/(2*p)-n*s.log(p)-(2+1/p)*loggamma_main
Mheadline = n*(s.log(2*s.pi)+(1+1/p)*s.log(1+p)/2-s.log(p)/2)
check('conjecture_5_1_constant', prefactor_main+headline-Mheadline)

base=Path(__file__).resolve().parent
out['scope']='Seven exact algebra/calculus checks; no numerical proof of DLMF or asymptotic estimates.'
out['sources']={'https://dlmf.nist.gov/10.41':hashlib.sha256((base/'sources/dlmf-10.41.html').read_bytes()).hexdigest()}
(base/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 7 exact identities; source hash bound.')
