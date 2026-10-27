"""Try exact shifted-coefficient certificates for the finite Davis range."""
from math import isqrt, factorial
from pathlib import Path
import sympy as s
import json
x=s.symbols('x')

def falling(i):
    return s.prod(x-j for j in range(i))

def P(d):
    fs=[s.Poly(falling(i),x,domain=s.QQ) for i in range(d+1)]
    return sum((fs[i]**2*fs[d-i]**2/s.Integer(factorial(i)*factorial(d-i)) for i in range(d+1)),s.Poly(0,x,domain=s.QQ))

last=None
rows=[]
for d in range(5,43):
    p=P(d) if last is None else last
    pn=P(d+1);last=pn
    q=2*x*x/s.Integer(d+1)-2*d*x/s.Integer(d+1)+s.Rational(d,2)
    f=s.Poly((2*x+d-2)*q-s.Rational(199,200)*(d-2),x)*p - s.Poly(2*x+d-2,x)*pn
    # Factor out only a square, positive at every x >= the threshold.
    common=s.Poly(falling((d+1)//2)**2,x,domain=s.QQ)
    f,rem=s.div(f,common);assert rem.is_zero
    r=s.Rational(d,2)+s.Rational(isqrt((d+2)*10**12),2*10**6)
    shifted=f.shift(r)
    neg=[i for i,v in enumerate(reversed(shifted.all_coeffs())) if v<0]
    row=dict(d=d,degree=f.degree(),threshold_below=str(r),negative_degrees=neg,
             all_coefficients_positive=all(v>0 for v in shifted.all_coeffs()))
    rows.append(row)
    print(row,flush=True)
Path(__file__).with_name('davis-polynomial-search.json').write_text(json.dumps(rows,indent=2)+'\n')
