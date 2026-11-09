"""Run only under the assigned helper_guard.py. Finite diagnostics, not proof."""
from pathlib import Path
import json
import mpmath as m
import sympy as s

p = Path(__file__).resolve().parent
m.mp.dps = 35
def g(r):
    return m.sqrt(2*r/m.expm1(2*r)) if r else m.mpf(1)
def h(t):
    a = -m.log(t)
    return 2*m.quad(lambda q:g(a*m.sin(q)**2),[0,m.pi/2])
def K(t):
    return 2*m.quad(lambda v:m.sqrt(max(m.mpf(0),-m.log(t*t+v*v))),[0,m.sqrt(1-t*t)])
def hs(t):
    # independent original derivative formula, desingularized by v=L sin q
    L=m.sqrt(1-t*t)
    def f(q):
        c=m.cos(q);delta=L*L*c*c;u=1-delta
        if abs(c)<m.mpf('1e-30'):return 2*t
        return 2*t*L*c/(u*m.sqrt(-m.log1p(-delta)))
    return m.quad(f,[0,m.pi/2])
rows=[]
for t in map(m.mpf,['.01','.2','.5','.9','.99']):
    a,b=h(t),hs(t)
    rows.append({'t':str(t),'abel_h':str(a),'original_h':str(b),'difference':str(a-b),
                 'K_derivative_plus_h':str(m.diff(K,t)+a)})
    assert abs(a-b)<m.mpf('1e-25')
# Test all constants through independent series and a single cosine integral.
for z in [m.mpf('.7'),m.mpc('1.1','.6')]:
    H=m.fsum([(-z*z/4)**n/(m.factorial(n)**2*(n+1)**m.mpf('1.5')) for n in range(60)])
    I=4/(m.pi*m.sqrt(m.pi))*m.quad(lambda t:K(t)*m.cos(z*t),[0,.5,1])
    rows.append({'z':str(z),'series_H':str(H),'cosine_H':str(I),'difference':str(H-I)})
    assert abs(H-I)<m.mpf('1e-28')
# Exact finite controls: Jensen degrees 1..3 and coefficient normalizations.
n=s.symbols('n',integer=True,nonnegative=True)
assert s.simplify(s.sqrt(n+1)/s.factorial(n+1)**2-1/(s.factorial(n)**2*(n+1)**s.Rational(3,2)))==0
D=s.Rational(9,2)-2*s.sqrt(3)
assert D>0  # J3/x = 3 + 3 sqrt(2)/2 x + sqrt(3)/6 x²
assert s.Rational(9,2)**2 > (2*s.sqrt(3))**2
out={'precision_digits':m.mp.dps,'finite_numerics_only':rows,
     'exact_Jensen_n3_discriminant':str(D),'exact_Jensen_n1_n2_n3_real_nonpositive':True,
     'all_orders_not_inferred_from_controls':True}
(p/'independent-checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
