"""ulas-review-r1: explicit polynomials r_{0,F}(m), F=0,1,2, in the monomial basis over Q
(exact Lagrange interpolation on m=1..D+1 using my own low-coefficient code, D = 4F+6 proved bound;
 verified on 15 further points)."""
import sys
from fractions import Fraction
src = open(sys.argv[1]).read().split("fails = 0")[0]
exec(src)  # defines v2, cheb_T_trunc, A2_low, r0_low (my verify_r0.py)
def interp(pts):
    n = len(pts); coeffs = [Fraction(0)] * n
    for i, (xi, yi) in enumerate(pts):
        basis = [Fraction(1)]; denom = Fraction(1)
        for j, (xj, _) in enumerate(pts):
            if j == i: continue
            basis = [Fraction(0)] + basis
            for k in range(len(basis) - 1): basis[k] -= xj * basis[k + 1]
            denom *= (xi - xj)
        for k in range(n): coeffs[k] += yi * basis[k] / denom
    return coeffs
for F in (0, 1, 2):
    D = 4 * F + 6
    pts = [(m, r0_low(m, F)[F]) for m in range(1, D + 2)]
    c = interp(pts)
    ev = lambda m: sum(ck * m ** k for k, ck in enumerate(c))
    ok = all(ev(m) == r0_low(m, F)[F] for m in range(D + 2, D + 17))
    deg = max(k for k, ck in enumerate(c) if ck != 0)
    import math
    L = 1
    for ck in c: L = L * ck.denominator // math.gcd(L, ck.denominator)
    print(f"r_(0,{F})(m) = (1/{L}) * [" + ", ".join(str(int(ck * L)) for ck in c[:deg + 1]) + f"]  (coeffs of m^0..m^{deg}); extra-point check {ok}")
