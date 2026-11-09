"""Verify: S_m(x) = sum_{k=1}^x k^m (x-k)^m is an odd polynomial of degree 2m+1
with leading coeff (m!)^2/(2m+1)!, and x^{2m+1} in span{S_0..S_m}."""
from fractions import Fraction
from math import comb, factorial
import sympy as sp

x = sp.Symbol('x')

def S_poly(m):
    """S_m as polynomial in x via S_m = sum_j C(m,j)(-1)^j x^{m-j} P_{m+j}(x)."""
    P = [sp.summation(sp.Symbol('k')**s, (sp.Symbol('k'), 1, x)) for s in range(2*m+1)]
    return sum(comb(m,j)*(-1)**j * x**(m-j) * P[m+j] for j in range(m+1))

def S_direct(m, n):
    return sum(k**m*(n-k)**m for k in range(1, n+1))

ok = True
for m in range(0, 9):
    S = sp.expand(S_poly(m))
    # check oddness
    isodd = sp.expand(S.subs(x, -x) + S) == 0
    # check degree/leading coeff
    lc = sp.Rational(factorial(m)**2, factorial(2*m+1))
    lead_ok = sp.LC(S, x) == lc
    # check against direct sums for n=1..25
    direct_ok = all(S.subs(x, n) == S_direct(m, n) for n in range(1, 26))
    print(f"m={m}: odd={isodd} lead={lead_ok} direct={direct_ok} S={S}")
    ok &= isodd and lead_ok and direct_ok
print("ALL ODDNESS/LEADING/DIRECT:", ok)

# Triangular solve: x^{2m+1} = sum_r A_{m,r} S_r ; compare with source values
for m in range(1, 8):
    Sr = [sp.expand(S_poly(r)) for r in range(m+1)]
    # solve for A coefficients: match coefficients of odd powers
    A = sp.symbols(f'a0:{m+1}')
    expr = sum(A[r]*Sr[r] for r in range(m+1)) - x**(2*m+1)
    poly = sp.Poly(sp.expand(expr), x)
    eqs = [sp.Eq(c, 0) for c in poly.all_coeffs()]
    sol = sp.solve(eqs, A, dict=True)[0]
    coeffs = [sp.simplify(sol[A[r]]) for r in range(m+1)]
    print(f"m={m}: A_{m,r} (r=0..m) = {coeffs}")
    # verify identity at integer points
    ident = all(sum(coeffs[r]*S_direct(r, n) for r in range(m+1)) == n**(2*m+1) for n in range(1, 40))
    print("   identity check n=1..39:", ident)
