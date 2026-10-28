"""Checks for an UNCOUNTED partial result, not a proof of Conjecture 2.

Run from anywhere; only this lane's checks.json is written. Exact symbolic
identities are separated from finite, high-precision numerical evidence.
"""
from pathlib import Path
import json
import hashlib
import mpmath as mp
import sympy as sp

HERE = Path(__file__).resolve().parent
mp.mp.dps = 70
u, S, a, alpha, beta = sp.symbols('u S a alpha beta', real=True)
h = sp.Function('h')
r = h(u) * h(S-u)
assert sp.simplify(sp.diff(r, u, 2) - (
    sp.diff(h(u), u, 2)*h(S-u)
    - 2*sp.diff(h(u), u)*sp.Subs(sp.diff(h(u), u), u, S-u)
    + h(u)*sp.Subs(sp.diff(h(u), u, 2), u, S-u))) == 0

exact = []
for k in range(20):
    hb2 = lambda t: t+1
    lhs = sum(hb2(a+alpha+i)*hb2(a+beta+k-i) for i in range(k+1))
    rhs = sum(hb2(a+i)*hb2(a+alpha+beta+k-i) for i in range(k+1))
    assert sp.expand(lhs-rhs-(k+1)*alpha*beta) == 0
    exact.append({'k': k, 'b2_coefficient': f'{k+1}*alpha*beta'})

h3 = lambda t: (t+1)*(t+2)/2
bad_curvature = sp.diff(h3(u)*h3(10-u), u, 2).subs(u, sp.Rational(1, 10))
assert bad_curvature == sp.Rational(2953, 100) > 0

def gamma_h(t, b):
    return mp.exp(mp.loggamma(t+b)-mp.loggamma(t+1)-mp.loggamma(b))

cases = []
for b0 in ['1.01', '1.1', '1.5', '1.9', '2']:
    b = mp.mpf(b0)
    for aa, al, be in [('0.01', '0.02', '0.03'),
                      ('0.3', '0.7', '0.2'),
                      ('3', '1.3', '2.7')]:
        av, alv, bev = map(mp.mpf, (aa, al, be))
        for k in [0, 1, 2, 5, 10, 30]:
            left = mp.fsum(gamma_h(av+alv+i, b)*gamma_h(av+bev+k-i, b)
                           for i in range(k+1))
            right = mp.fsum(gamma_h(av+i, b)*gamma_h(av+alv+bev+k-i, b)
                            for i in range(k+1))
            assert left > right
            cases.append({'b': b0, 'a': aa, 'alpha': al, 'beta': be,
                          'k': k, 'relative_gap': mp.nstr((left-right)/left, 30)})

result = {
    'scope': 'UNCOUNTED partial range 1<b<=2; not full Conjecture 2',
    'symbolic_product_second_derivative': 'PASS',
    'exact_b2_identities': exact,
    'b3_s10_u1_over_10_second_derivative': str(bad_curvature),
    'numerical_evidence_only': cases,
    'numeric_cases': len(cases),
    'proof': 'PARTIAL.md; finite checks are not the proof',
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
(HERE/'checks.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'exact_b2_identities': len(exact), 'numeric_cases': len(cases),
                  'b3_concavity_shortcut': 'REFUTED', 'credit': 0}))
