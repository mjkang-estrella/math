"""Independent low-order symbolic checks; no all-order claim."""
import json
from math import factorial, comb
from pathlib import Path
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

u, v = s.symbols('u v', real=True)
N = 9
P = lambda x, k: s.prod(x-j*(j+1) for j in range(k))
C = [s.expand(sum(comb(k,j)*P(u,j)*P(v,k-j)*(1+s.I)**j*(1-s.I)**(k-j)
                  for j in range(k+1))) for k in range(N+1)]
A = [s.Integer(1)] + [s.expand(sum(2**(n-k)*(factorial(n)//factorial(k))*
     stirling(n,k,kind=2)*C[k] for k in range(1,n+1))) for n in range(1,N+1)]
B = [s.Integer(0)]
rows = []
for n in range(1,N+1):
    B.append(s.expand(A[n]-sum(comb(n-1,k-1)*B[k]*A[n-k] for k in range(1,n))))
    im = s.expand(s.im(B[n]))
    assert s.expand(B[n].subs({u:v,v:u}, simultaneous=True)-s.conjugate(B[n])) == 0
    row = {'n':n, 'imaginary_part':str(s.factor(im))}
    if n % 2:
        W = im.subs(u,0)-im.subs({u:0,v:u}, simultaneous=True)
        K = s.expand(im-W)
        R = s.Poly(s.cancel(K/(u*v*(u-v))), u,v,domain=s.ZZ)
        assert s.expand(R.as_expr()-R.as_expr().subs({u:v,v:u}, simultaneous=True)) == 0
        row['R'] = str(s.factor(R.as_expr()))
    else:
        assert im == 0
    rows.append(row)

# Swap/conjugation alone does NOT force even-index imaginary parts to vanish.
t = s.symbols('t', real=True)
F = 1+s.I*(u-v)*t**2
assert s.expand(F.subs({u:v,v:u}, simultaneous=True)-s.conjugate(F)) == 0
assert s.expand(s.im(F*F.subs(t,-t))-2*(u-v)*t**2) == 0
# Minimum valuation need not occur in the highest pure coefficient.
# m=2: this antisymmetric polynomial has content 2^6, but its v^3 coefficient has valuation 7.
f = 64*(u-v)+128*(u**3-v**3)
assert s.Poly(f,u,v).content() == 64
assert s.Poly(f,u,v).coeff_monomial(v**3) == -128
out = {'scope':'finite n<=9 only', 'rows':rows,
       'swap_does_not_imply_even_reality':True,
       'minimum_does_not_identify_top_coefficient':True}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: n<=9 exact checks and two logical counterexamples; no all-order proof.')
