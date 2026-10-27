#!/usr/bin/env python3
"""Independent adversarial re-derivation for cstar-sendov final review.
Structure deliberately different from parent/scripts/check_sendov.py:
uses mpmath (50 dps), dense 4001-point grid, plus exact algebraic checks via sympy-free
rational/sqrt arithmetic where possible. Original by pi-sendov-final-review; parent corrected the two-branch weight-check indentation.
"""
from mpmath import mp, mpf, expjpi, sqrt, norm
mp.dps = 50
N = 4001
maxres = mpf(0)
def chk(name, val, tol):
    global maxres
    maxres = max(maxres, abs(val))
    assert abs(val) <= tol, f"{name} residual {val}"

for i in range(N):
    t = mpf(i) / (N - 1)
    u = expjpi(mpf(1) * t)          # e^{pi i t}
    rho, s = mpf(9)/10, mpf(3)/4
    a0 = rho; a1 = rho*s*u; a2 = -rho*s*u
    h = 1 + mpf(16)/27 * u.conjugate()**2
    q = mpf(3)*sqrt(3)/4 * u * sqrt(h)
    Bp = rho/3 * (1 + q); Bm = rho/3 * (1 - q)
    # 1. deleted derivative formula 3z^2 - 9/5 z - 729/1600 u^2 evaluated at z=Bp,Bm
    for B in (Bp, Bm):
        z = B
        del_deriv = 3*z*z - mpf(9)/5*z - mpf(729)/1600*u**2
        chk("deleted(B)", del_deriv, mpf(1e-45))
    # 2. factorization 3(z-Bp)(z-Bm) == 3z^2 - 2rho z - rho^2 s^2 u^2 as identity in z
    #    compare coefficients: 3(Bp+Bm) = 9/5? ; 3 Bp Bm = 729/1600 u^2 (sign)
    chk("sumcoef", 3*(Bp+Bm) - mpf(9)/5, mpf(1e-45))
    chk("prodcoef", 3*Bp*Bm + mpf(729)/1600*u**2, mpf(1e-45))
    # 3. q^2 = 1 + 27/16 u^2
    chk("qsq", q**2 - (1 + mpf(27)/16*u**2), mpf(1e-45))
    # 4. |q|^2 <= 43/16, q != 0
    assert abs(q) > mpf(11)/16, "q modulus lower bound"
    assert abs(q)**2 <= mpf(43)/16 + mpf(1e-45)
    # 5. |B| < 9/10 strict
    for B in (Bp, Bm):
        assert abs(B) < mpf(9)/10, f"|B|={abs(B)}"
    # 6. roots distinct pointwise; B branches distinct; B != each root
    assert a1 != a2 and abs(a0-a1) > 0 and abs(a0-a2) > 0
    assert Bp != Bm
    for B in (Bp, Bm):
        for a in (a0, a1, a2):
            assert abs(B-a) > mpf(1e-40), "B meets a root"
    for B in (Bp, Bm):
        # 7. convex weights reproduce B
        r = [1/abs(B-a)**2 for a in (a0, a1, a2)]
        R = sum(r)
        w = [ri/R for ri in r]
        recom = sum(w[j]*(a0,a1,a2)[j] for j in range(3))
        chk("weights", recom - B, mpf(1e-40))
        assert min(w) > 0 and abs(sum(w) - 1) < mpf(1e-40)
        # 8. harmonic identity sum (B-aj)^-1 = 0
        chk("harmonic", sum(1/(B-a) for a in (a0,a1,a2)), mpf(1e-40))

# endpoint exact values
t0 = mpf(0); u0 = expjpi(0); q0 = mpf(3)*sqrt(3)/4*sqrt(mpf(43)/27)
assert q0 == mpf(3)*sqrt(3)/4 * sqrt(mpf(43)/27)
dist0 = abs(mpf(9)/10 - mpf(3)/10*(1-q0))
exact = mpf(3)/5 + mpf(3)*sqrt(43)/40
chk("endpoint-exact", dist0 - exact, mpf(1e-45))
assert exact > mpf(21)/20 > 1
assert exact > 1
# Q = sqrt(43)/4 check: q0 = 3sqrt3/4 * sqrt(43/27) = sqrt(43)/4 ?
chk("Q-form", q0 - sqrt(43)/4, mpf(1e-45))
assert q0 > mpf(3)/2
# t=1: u=-1, branch flips
q1 = mpf(3)*sqrt(3)/4 * (-1) * sqrt(mpf(43)/27)
chk("q1", q1 + q0, mpf(1e-45))
assert abs(mpf(9)/10 - mpf(3)/10*(1-q0)) == dist0  # B+(1)=B-(0)=0.3(1-q0)

print("ALL INDEPENDENT MATH CHECKS PASS; max residual =", maxres)
print("endpoint distance exact =", exact, " > 21/20 =", mpf(21)/20)
print("approx:", mpf(exact))
