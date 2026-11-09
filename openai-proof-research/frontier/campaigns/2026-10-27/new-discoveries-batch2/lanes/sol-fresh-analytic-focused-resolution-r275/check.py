"""Exact certificates for an EXCLUDED rediscovery; run only through helper_guard.py."""
from pathlib import Path
import json
import sympy as s

p = Path(__file__).resolve().parent
z, v, q, t = s.symbols('z v q t')
certificates = []
for N in range(4, 40, 3):
    P = sum(s.binomial(N,j)*z**j*(1-z)**(N-j) for j in range(2,N+1,3))
    V = s.Poly(s.expand((z*(1-z)*P).subs(z,(1-v)/2)),v)
    assert all(mon[0] % 2 == 0 for mon,c in V.terms())
    W = s.Poly(sum(c*(1-q)**(mon[0]//2) for mon,c in V.terms()),q)
    assert s.expand(W.as_expr().subs(q,4*z*(1-z))-z*(1-z)*P) == 0
    D = s.Poly(s.cancel(s.diff(W.as_expr(),q)/q**2),q)
    intervals = [(s.Rational(0),s.Rational(1))]
    if N in (10,13):
        intervals = [(s.Rational(0),s.Rational(1,2)),(s.Rational(1,2),s.Rational(1))]
    pieces = []
    for lo,hi in intervals:
        R = s.Poly(D.as_expr().subs(q,lo+(hi-lo)*t),t)
        d = R.degree()
        b = [sum(R.nth(k)*s.binomial(i,k)/s.binomial(d,k) for k in range(i+1)) for i in range(d+1)]
        assert all(x >= 0 for x in b)
        assert s.expand(sum(b[i]*s.binomial(d,i)*t**i*(1-t)**(d-i) for i in range(d+1))-R.as_expr()) == 0
        pieces.append({'interval':[str(lo),str(hi)],'bernstein':[str(x) for x in b]})
    certificates.append({'N':N,'derivative_divided_by_q_squared':str(D.as_expr()),'pieces':pieces})
assert sum(s.Rational(7,2)**k/s.factorial(k) for k in range(7)) > s.Rational(39,2)
assert 1602*s.Rational(2,3)**38 < 1
assert 3*40*39*s.Rational(1,42**2) >= s.Rational(5,2)
(p/'exact-certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
print('PASS: 12 exact degree certificates, subdivision identities, rational tail constants')
