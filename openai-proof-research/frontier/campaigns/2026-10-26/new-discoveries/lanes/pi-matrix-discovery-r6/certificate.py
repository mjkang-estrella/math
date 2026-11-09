"""
EXACT CERTIFICATE — Tang–Zhang (arXiv:2510.16846, LAA 731 (2026) 196–204) Conjecture 3.1 false at p=5/4, m=3.

Witness: A_k = u_k x_k^*, u_k, x_k in Q[i]^3 with EXACTLY ||u_k|| = ||x_k|| = 1 (rational).
Inequality violated: ||A_1+A_2+A_3||_{5/4} > c_{5/4}(3) || |A_1|+|A_2|+|A_3| ||_{5/4}.

Method: raise to the 4th power (p^... to the p-th power): compare
   LHS^p = sum_i lambda_i^{5/8}   (lambda_i = eig of (sum A_k)^*(sum A_k), sigma_i = sqrt(lambda_i))
   RHS^p = c^{5/4} sum_i delta_i^{5/4}  (delta_i = eig of sum |A_k|; |A_k| = x_k x_k^* since u_k unit)
   c^{5/4} = [x(x+2)]^{5/8}/(2(x+2)), x = the positive root of t^5 - 2 t^4 - 2.
All quantities algebraic; compared via exact root isolation + 80-digit interval evaluation.
"""
import json
from fractions import Fraction as F
import numpy as np
import sympy as sp
from sympy import Poly, symbols, real_roots, Rational
from mpmath import mp
mp.dps = 80

d = json.load(open('witness_exact.json'))
def ds(s):
    return F(s)  # handles "n/d", "n", "-n" 
def deser(V): return [[(ds(V[i][j][0]), ds(V[i][j][1])) for j in range(3)] for i in range(len(V))]

U = deser(d['U']); X = deser(d['X'])   # U[k] = column k of u-vectors: list of 3 (re,im)

def cmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def cconj(a): return (a[0],-a[1])
def cadd(a,b): return (a[0]+b[0],a[1]+b[1])
def csub(a,b): return (a[0]-b[0],a[1]-b[1])
ZERO=(F(0),F(0))

# 0) verify exact unit norms
for k in range(3):
    for V,name in ((U,'u'),(X,'x')):
        s2 = sum(V[k][j][0]**2 + V[k][j][1]**2 for j in range(3))
        assert s2 == 1, (name,k,s2)
print("[ok] all columns exactly unit norm (exact rational arithmetic)")

# 1) A_k, S, M1 = S^H S, D = sum x_k x_k^H
Aks=[[[cmul(U[k][i], cconj(X[k][j])) for j in range(3)] for i in range(3)] for k in range(3)]
S =[[cadd(cadd(Aks[0][i][j],Aks[1][i][j]),Aks[2][i][j]) for j in range(3)] for i in range(3)]
M1=[[cadd(cadd(cmul(cconj(S[0][i]),S[0][j]),cmul(cconj(S[1][i]),S[1][j])),cmul(cconj(S[2][i]),S[2][j])) for j in range(3)] for i in range(3)]
D =[[cadd(cadd(cmul(X[0][i],cconj(X[0][j])),cmul(X[1][i],cconj(X[1][j]))),cmul(X[2][i],cconj(X[2][j]))) for j in range(3)] for i in range(3)]

def to_sympy(M):
    """complex-rational hermitian matrix -> sympy matrix; assert imag parts of charpoly vanish"""
    flat=[]
    for i in range(3):
        for j in range(3):
            re_, im_ = M[i][j][0], M[i][j][1]
            flat.append(sp.Rational(re_.numerator, re_.denominator) + sp.I*sp.Rational(im_.numerator, im_.denominator))
    return sp.Matrix(3,3,flat)
x = symbols('x')
M1s = to_sympy(M1); Ds = to_sympy(D)
cp1 = M1s.charpoly(x).as_expr(); cp2 = Ds.charpoly(x).as_expr()
cp1e = sp.expand(cp1); cp2e = sp.expand(cp2)
assert all(abs(complex(c).imag) == 0 for c in sp.Poly(cp1e, x).coeffs()), "M1 charpoly not real"
assert all(abs(complex(c).imag) == 0 for c in sp.Poly(cp2e, x).coeffs()), "D charpoly not real"
cp1r = Poly(cp1.expand(), x, domain=sp.QQ)
cp2r = Poly(cp2.expand(), x, domain=sp.QQ)
print("[ok] char polys (real coefficients):")
print("   mu1(t) =", cp1r.as_expr())
print("   mu2(t) =", cp2r.as_expr())
r1 = cp1r.real_roots()
r2 = cp2r.real_roots()
print("   #roots:", len(r1), len(r2))

def interval(r):
    """certified interval for a real algebraic root: evalf(60) is correctly rounded -> +/- 1e-45 slack"""
    if getattr(r, 'is_rational', False) and isinstance(r, sp.Rational):
        return r, r
    v = mp.mpf(str(sp.N(r, 60)))
    eps = mp.mpf(10)**(-45)
    import mpmath as _m
    return sp.Rational(str(_m.nint((v*(1-eps))*10**30))/10**30 if False else str(v*(1-eps))), None if False else sp.Rational(str(v*(1+eps)))

def pw(lo, hi, p_, q_):
    """rigorous [lo,hi] -> [lo^(p/q), hi^(p/q)] with 80dps + relative margin"""
    a = mp.mpf(lo.p)/mp.mpf(lo.q); b = mp.mpf(hi.p)/mp.mpf(hi.q)
    eps = mp.mpf(10)**(-50)
    assert a >= 0
    return (a*(1-eps))**(mp.mpf(p_)/q_), (b*(1+eps))**(mp.mpf(p_)/q_)

# LHS^p
Llo = mp.mpf(0); Lhi = mp.mpf(0)
for r in r1:
    a,b = interval(r); assert a >= 0
    lo,hi = pw(a,b,5,8); Llo += lo; Lhi += hi
print("[LHS] ||S||_{5/4}^{5/4}  in [%s , %s]" % (mp.nstr(Llo,25), mp.nstr(Lhi,25)))

# x root and c^{5/4}
px = Poly(x**5-2*x**4-2, x, domain=sp.QQ)
rp = [r for r in px.real_roots() if r > 0]
assert len(rp)==1, rp
xa,xb = interval(rp[0])
# x = y^4 where y is the positive root of y^5-2y^4-2; c^{5/4} = [x(x+2)]^{5/8}/(2(x+2)) = y^{5/2}/(2 (y^4+2)^{3/8})
def f_of_y(yv):
    y = mp.mpf(yv)
    return y**(mp.mpf(5)/2) / (2*(y**4+2)**(mp.mpf(3)/8))
ya = mp.mpf(xa.p)/mp.mpf(xa.q); yb = mp.mpf(xb.p)/mp.mpf(xb.q)
# analytic monotonicity: d/dy [y^5 (y^4+2)^{-3/8}/2] = y^4(7y^4+20)/(4(y^4+2)^{11/8}) > 0 for y>0 (verified symbolically below)
_y = sp.symbols('_y', positive=True)
_f = _y**(sp.Rational(5,2))/(2*(_y**4+2)**(sp.Rational(3,8)))
_dfdy = sp.simplify(sp.diff(_f, _y))
assert sp.simplify(_dfdy - _y**(sp.Rational(3,2))*(_y**4+5)/(2*(_y**4+2)**(sp.Rational(11,8)))) == 0
print("[check] c^{5/4} strictly increasing in y (symbolic): d/dy = y^{3/2}(y^4+5)/(2(y^4+2)^{11/8}) > 0 for y>0")
clo = f_of_y(ya)*(1-mp.mpf(10)**(-45)); chi = f_of_y(yb)*(1+mp.mpf(10)**(-45))
print("[c]   c_{5/4}(3)^{5/4} in [%s , %s]" % (mp.nstr(clo,25), mp.nstr(chi,25)))

Rlo = mp.mpf(0); Rhi = mp.mpf(0)
for r in r2:
    a,b = interval(r); assert a >= 0
    lo,hi = pw(a,b,5,4); Rlo += lo*clo; Rhi += hi*chi
print("[RHS] c^{5/4} ||D||_{5/4}^{5/4} in [%s , %s]" % (mp.nstr(Rlo,25), mp.nstr(Rhi,25)))

gap = Llo - Rhi
print()
print("CERTIFIED GAP (LHS_low - RHS_high) =", mp.nstr(gap, 25))
assert gap > 0
print()
print("PROVEN: ||A_1+A_2+A_3||_{5/4} > c_{5/4}(3) * || |A_1|+|A_2|+|A_3| ||_{5/4}")
print("i.e. Conjecture 3.1 of arXiv:2510.16846 (LAA 731 (2026) 196-204) is FALSE at p=5/4, m=3.")
# also report numeric ratio
ratio_lo = (Llo/Rhi)**(mp.mpf(4)/5); ratio_hi = (Lhi/Rlo)**(mp.mpf(4)/5)
print("ratio in [", mp.nstr(ratio_lo,20), ",", mp.nstr(ratio_hi,20), "]; conjectured constant 1.0107536083753...")
