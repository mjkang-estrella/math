from fractions import Fraction
from math import comb, factorial
import sympy as sp
x = sp.Symbol('x')
def S_poly(m):
    P = [sp.summation(sp.Symbol('k')**s, (sp.Symbol('k'), 1, x)) for s in range(2*m+1)]
    return sum(comb(m,j)*(-1)**j * x**(m-j) * P[m+j] for j in range(m+1))
def S_direct(m, n):
    return sum(k**m*(n-k)**m for k in range(1, n+1))

for m in range(1, 9):
    Sr = [sp.expand(S_poly(rr)) for rr in range(m+1)]
    A = sp.symbols(f'a0:{m+1}')
    expr = sp.Poly(sp.expand(sum(A[rr]*Sr[rr] for rr in range(m+1)) - x**(2*m+1)), x)
    sol = sp.solve([sp.Eq(c,0) for c in expr.all_coeffs()], A, dict=True)[0]
    coeffs = [sp.nsimplify(sp.simplify(sol[A[rr]])) for rr in range(m+1)]
    ident = all(sum(int(coeffs[rr])*S_direct(rr, n) for rr in range(m+1)) == n**(2*m+1) for n in range(1, 60))
    print(f"m={m}: A_m_r r=0..{m} = {coeffs}  identity(n=1..59)={ident}")

# Source cross-checks (Kolosov displayed identities):
# x^3 = 6 S_1 + S_0 ; x^5 = 30 S_2 + S_0 ; x^7 = 140 S_3 - 14 S_1 + S_0
# x^9 = 630 S_4 - 120 S_1 + S_0 ; x^11 = 2772 S_5 + 660 S_2 - 1386 S_1 + S_0
checks = [
 (1, {1:6, 0:1}), (2, {2:30, 0:1}), (3, {3:140, 1:-14, 0:1}),
 (4, {4:630, 1:-120, 0:1}), (5, {5:2772, 2:660, 1:-1386, 0:1}),
 (6, {6:51480, 3:-60060, 2:491400, 1:-450054, 0:1}),  # note source x^13 uses k^5(x-k)^7 typo row; we test corrected
]
for m, d in checks[:6]:
    Sr = [sp.expand(S_poly(rr)) for rr in range(m+1)]
    lhs = sum(v*Sr[rr] for rr, v in d.items())
    print(f"m={m} source coeff check: {sp.expand(lhs - x**(2*m+1)) == 0}")
