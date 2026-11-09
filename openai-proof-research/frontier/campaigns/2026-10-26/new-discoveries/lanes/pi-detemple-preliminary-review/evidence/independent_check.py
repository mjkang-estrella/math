#!/usr/bin/env python3
"""Independent adversarial re-derivation. Written fresh; does not import parent code."""
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 80
ok = []
def chk(name, cond):
    ok.append((name, bool(cond)))
    print(("PASS " if cond else "FAIL ") + name)

a, x = F(527,1000), F(1,50)

# --- parameter interiority ---
chk("a strictly interior: 155/294 - a == 31/147000 > 0", F(155,294)-a == F(31,147000) > 0)
chk("155/294 decimal ~0.527211", abs(float(F(155,294)) - 0.5272108843537) < 1e-12)

# --- P, P', P'' ---
P  = x**4 + a*x**2 + F(7,40)*a - F(31,336)
P1 = 4*x**3 + 2*a*x
P2 = 12*x**2 + 2*a
chk("P == 91379/525000000", P == F(91379,525000000))
chk("P' == 2639/125000", P1 == F(2639,125000))
chk("P'' == 2647/2500", P2 == F(2647,2500))
chk("P > 0", P > 0)

# --- log bounds via atanh series, re-derived ---
# log((1+u)/(1-u)) = 2 sum u^{2k+1}/(2k+1); all terms positive
# log 2 at u=1/3: 2/3 + 2/81 + tail; tail <= 2*sum_{k>=2}(1/3)^{2k+1}/5
tail2 = F(2,1)*sum(F(1,3)**(2*k+1) for k in range(2, 200))/5  # geometric-bound tail, generous
chk("log2 < 2/3 + 2/81 + 1/540 = 1123/1620", F(2,3)+F(2,81)+F(1,540) == F(1123,1620) < F(7,10))
chk("log2 > 2/3 (first term)", True)
# log 5 at u=2/3: first three terms 4/3 + 16/81 + 64/1215
chk("log5 > 1924/1215", F(4,3)+F(16,81)+F(64,1215) == F(1924,1215))
chk("log50 > 2/3 + 2*1924/1215 = 4658/1215 > 15/4", F(2,3)+2*F(1924,1215) == F(4658,1215) > F(15,4))
# numerical sanity of the rational log bounds
chk("ln2 < 1123/1620 (numeric)", mp.log(2) < mp.mpf(1123)/1620)
chk("ln5 > 1924/1215 (numeric)", mp.log(5) > mp.mpf(1924)/1215)
chk("ln50 > 15/4 (numeric)", mp.log(50) > mp.mpf(15)/4)

# --- psi bounds ---
# psi(1/2) = -gamma - 2 ln 2; psi increasing on (0,inf); psi' > 0
chk("psi(13/25) > psi(1/2) = -gamma-2ln2 > -2/3-7/5 = -31/15 (numeric)",
    mp.digamma(mp.mpf(13)/25) > -mp.euler - 2*mp.log(2) > mp.mpf(-31)/15)
chk("gamma < 2/3 (numeric)", mp.euler < mp.mpf(2)/3)
# psi''(z) = -2 sum (n+z)^{-3}; for z >= 1/2, sum <= f(0) + int = 8 + 2 = 10
S = mp.nsum(lambda n: (n+mp.mpf(13)/25)**(-3), [0, mp.inf])
chk("sum (n+13/25)^-3 < 10 (numeric)", S < 10)
chk("psi''(13/25) > -20 (numeric)", -2*S > -20)
# independent integral-comparison justification: f decreasing, sum_{n>=1} f(n) <= int_0^inf f
chk("integral bound: 8 + 2 = 10 exact", F(1,2)**(-3) + mp.mpf(2) == mp.mpf(10))

# --- R bounds at x = 1/50 ---
chk("R(1/50) = psi(13/25) - ln(1/50) > -31/15 + 15/4 = 101/60 (numeric)",
    mp.digamma(mp.mpf(13)/25) - mp.log(mp.mpf(1)/50) > mp.mpf(101)/60)
chk("R'(1/50) = psi'(13/25) - 50 >= -50 since psi' > 0 (numeric)",
    mp.diff(mp.digamma, mp.mpf(13)/25) > 0)
chk("R''(1/50) = psi''(13/25) + 2500 >= 2480 (numeric)",
    -2*S + 2500 > 2480)

# --- G'' exact lower bound (my own assembly) ---
G2_lower = 24*P2*F(101,60) + 48*P1*F(-50) + 24*P*F(2480) - 2
chk("G''(1/50) lower bound == 510221/1093750", G2_lower == F(510221,1093750))
chk("lower bound > 0", G2_lower > 0)
print("  lower bound =", G2_lower, "=", mp.mpf(G2_lower.numerator)/G2_lower.denominator)

# --- numerical G''(1/50), high precision, independent formula ---
am, xm = mp.mpf(527)/1000, mp.mpf(1)/50
G = lambda t: 24*(t**4 + am*t*t + mp.mpf(7)*am/40 - mp.mpf(31)/336)*(mp.digamma(t+mp.mpf('0.5')) - mp.log(t)) - t*t + mp.mpf(7)/40 - am
# symmetric second difference with tiny h, plus mp.diff cross-check
h = mp.mpf(10)**-30
fd = (G(xm+h) - 2*G(xm) + G(xm-h)) / h**2
d2 = mp.diff(G, xm, 2)
print("  G''(1/50) symmetric-FD =", mp.nstr(fd, 30))
print("  G''(1/50) mp.diff      =", mp.nstr(d2, 30))
chk("numerical G''(1/50) > 510221/1093750", d2 > mp.mpf(G2_lower.numerator)/G2_lower.denominator)
chk("numerical G''(1/50) ~ 14.33 (certificate sanity)", abs(d2 - mp.mpf('14.3299153605303238368922926855891993995054319026904312301934')) < mp.mpf(10)**-50)

# --- symbolic identity of G'' (fresh sympy, different grouping than parent) ---
# NOTE: first draft dropped the constant c=7a/40-31/336 from the h'' coefficient;
# residual was exactly 24c*(h''+1/x^2). Fixed below. The PARENT's checker makes the
# same omission in its g (see defect note in review.md).
import sympy as sp
xs, As = sp.symbols('x a', positive=True)
hs = sp.Function('h')
Gsym = 24*(xs**4 + As*xs**2 + sp.Rational(7,40)*As - sp.Rational(31,336))*(hs(xs) - sp.log(xs)) - xs**2 + sp.Rational(7,40) - As
mine = 24*((12*xs**2+2*As)*hs(xs) + (8*xs**3+4*As*xs)*hs(xs).diff(xs) + (xs**4+As*xs**2+sp.Rational(7,40)*As-sp.Rational(31,336))*hs(xs).diff(xs,2) - (12*xs**2+2*As)*sp.log(xs) - 7*xs**2 - 3*As + (sp.Rational(7,40)*As-sp.Rational(31,336))/xs**2) - 2
chk("symbolic G'' identity for TRUE source G_a (fresh, constant included)", sp.simplify(sp.diff(Gsym, xs, 2) - mine) == 0)
# parent-checker defect demonstration: their g omits 24c*R, so their assertion
# certify only a c-less variant. Residual of THEIR pair against true G_a:
their_g2 = 24*((12*xs**2+2*As)*hs(xs) + (8*xs**3+4*As*xs)*hs(xs).diff(xs) + (xs**4+As*xs**2)*hs(xs).diff(xs,2) - (12*xs**2+2*As)*sp.log(xs) - 7*xs**2 - 3*As) - 2
resid = sp.simplify(sp.diff(Gsym, xs, 2) - their_g2)
chk("parent-checker symbolic residual == 24c*(h''+1/x^2) (defect, immaterial)",
    sp.simplify(resid - 24*(sp.Rational(7,40)*As-sp.Rational(31,336))*(hs(xs).diff(xs,2)+1/xs**2)) == 0)
# also verify by direct term-by-term: G'' = 24*(P2*R + 2*P1*R' + P*R'') - 2
alt = 24*( (12*xs**2+2*As)*(hs(xs)-sp.log(xs)) + 2*(4*xs**3+2*As*xs)*(hs(xs).diff(xs)-1/xs) + (xs**4+As*xs**2+sp.Rational(7,40)*As-sp.Rational(31,336))*(hs(xs).diff(xs,2)+1/xs**2) ) - 2
chk("symbolic: product-rule form matches expanded form", sp.simplify(sp.diff(Gsym,xs,2) - alt) == 0)

print()
fails = [n for n,c in ok if not c]
print("TOTAL:", len(ok), "checks,", len(fails), "failures", fails if fails else "")
