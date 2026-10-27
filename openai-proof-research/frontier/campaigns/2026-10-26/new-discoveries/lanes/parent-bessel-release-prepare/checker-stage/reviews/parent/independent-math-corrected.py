#!/usr/bin/env python3
"""INDEPENDENT exact math checker for the Bessel-Fejer candidate.
Written from scratch by the final-review agent; does NOT import or reuse
exact_bessel_certificate.py logic. All arithmetic in exact Fractions unless
stated. Cross-checks against high-precision mpmath at the end.
"""
from fractions import Fraction as F
import math, json, sys
from pathlib import Path

ok = True
def check(name, cond, detail=""):
    global ok
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
    if not cond: ok = False

# ---------- series and coefficients ----------
N = 20  # terms k=0..19
def p(q):  # partial J0 series in q=x^2/4
    s = F(0); term = F(1)
    for k in range(N):
        if k > 0: term = term * (-q) / (F(k)*F(k))
        s += term
    return s
def h(q):  # partial H series
    s = F(0); term = F(1)
    for k in range(N):
        if k > 0: term = term * (-q) / (F(k)*F(k+1))
        s += term
    return s

E  = F(2*9**20, math.factorial(20)**2)        # tail bound J0, |x|<=6
EH = F(2*9**20, math.factorial(20)*math.factorial(21))  # tail bound H
check("tail bounds positive", E > 0 and EH > 0, f"e={float(E):.3e} eH={float(EH):.3e}")
check("tail ratio < 1/2", F(9, 21*21) < F(1,2))
check("e < 1e-17", E < F(1, 10**17))
check("eH < 1e-18", EH < F(1, 10**18))

# exact tail-bound justification (independent derivation):
# J0 series term T_k = q^k/(k!)^2; for k>=20 ratio <= q/(k+1)^2 <= 9/441.
# |tail| <= T_20 * sum_{j>=0} r^j with r=9/441 => T_20 * 441/432 < 2*T_20. OK by inspection.

# ---------- Bernstein bound verifier (own implementation) ----------
def bernstein_minmax(coeffs, a, b):
    """Exact min/max Bernstein coefficients of P(q)=sum a_r q^r on [a,b].
    beta_i = sum_{k=0..i} binom(i,k)/binom(d,k) (b-a)^k sum_{r=k..d} a_r binom(r,k) a^{r-k}"""
    d = len(coeffs) - 1
    betas = []
    for i in range(d+1):
        beta = F(0)
        for k in range(i+1):
            inner = F(0)
            for r in range(k, d+1):
                inner += coeffs[r] * F(math.comb(r, k)) * (a ** (r - k))
            beta += F(math.comb(i, k), math.comb(d, k)) * ((b - a) ** k) * inner
        betas.append(beta)
    return min(betas), max(betas)

def p_coeffs():
    c = []
    for k in range(N):
        c.append(F((-1)**k, math.factorial(k)**2))
    return c
def h_coeffs():
    c = []
    for k in range(N):
        c.append(F((-1)**k, math.factorial(k)*math.factorial(k+1)))
    return c

pc, hc = p_coeffs(), h_coeffs()
L1, U1 = F("2.4048"), F("2.4049")
L2, U2 = F("5.5200"), F("5.5201")
c = F(47, 50)

# Table row 1: h(q) >= 1/5 on [0, 9/4]
mn, mx = bernstein_minmax(hc, F(0), F(9,4))
check("row1 h>=1/5 on [0,9/4]", mn >= F(1,5), f"min beta={float(mn):.6f}")
# Row 2: p(q) <= -1/50000 on [9/4, L2^2/4]
mn, mx = bernstein_minmax(pc, F(9,4), L2*L2/4)
check("row2 p<=-1/50000 on [9/4,L2^2/4]", mx <= F(-1,50000), f"max beta={float(mx):.8f}")
# Row 3: h(q) <= -3/25 on [L2^2/4, U2^2/4]
mn, mx = bernstein_minmax(hc, L2*L2/4, U2*U2/4)
check("row3 h<=-3/25 on [L2^2/4,U2^2/4]", mx <= F(-3,25), f"max beta={float(mx):.6f}")
# Row 4: p(q) <= 3081/40000 on [(c L1)^2/4, (c U1)^2/4]
mn, mx = bernstein_minmax(pc, (c*L1)**2/4, (c*U1)**2/4)
check("row4 p<=3081/40000", mx <= F(3081,40000), f"max beta={float(mx):.8f}")
# Row 5: p(q) <= -11381/100000 on [(c L2)^2/4, (c U2)^2/4]
mn, mx = bernstein_minmax(pc, (c*L2)**2/4, (c*U2)**2/4)
check("row5 p<=-11381/100000", mx <= F(-11381,100000), f"max beta={float(mx):.8f}")

# ---------- endpoint sign checks for zeros (direct rational evaluation) ----------
def J_interval(x_lo, x_hi):
    """[p(x^2/4)-E, p(x_hi^2/4)+E] valid enclosure of J0 over [x_lo,x_hi]?
    Instead: evaluate p at both endpoints, use monotone p? p is not monotone
    in general, so use interval Horner for p on the q-range."""
    lo, hi = interval_horner(pc, x_lo*x_lo/4, x_hi*x_hi/4)
    return lo - E, hi + E

def interval_horner(coeffs, qlo, qhi):
    """Exact interval evaluation of polynomial by Horner on [qlo,qhi]."""
    acc_hi = coeffs[-1]; acc_lo = coeffs[-1]
    for a in reversed(coeffs[:-1]):
        candidates = [acc_lo*qlo, acc_lo*qhi, acc_hi*qlo, acc_hi*qhi]
        acc_lo, acc_hi = min(candidates), max(candidates)
        acc_lo, acc_hi = acc_lo + a, acc_hi + a
    return acc_lo, acc_hi

J1l, J1h = J_interval(L1, L1)  # point evaluations as degenerate intervals
check("J0(2.4048)>0", J1l > 0, f"lo={float(J1l):.3e}")
J1l2, _ = J_interval(U1, U1)
check("J0(2.4049)<0", J1l2 + 2*E < 0, f"hi={float(J1l2):.3e}")
J2l, _ = J_interval(L2, L2)
check("J0(5.5200)<0", J2l + 2*E < 0, f"hi={float(J2l):.3e}")
_, J2h = J_interval(U2, U2)
check("J0(5.5201)>0", J2h - 2*E > 0, f"lo={float(J2h):.3e}")
# J0(0)=1 and J0(3)<0 (strictly decreasing on [0,3] from row1 => H>0 on q<=9/4)
_, J3h = J_interval(F(3), F(3))
check("J0(3)<0", J3h + 2*E < 0)

# ---------- fifth-power / square exact inequalities ----------
check("1.4204^5 < 2.4048^2", F("1.4204")**5 < L1*L1)
check("2.4049^2 < 1.4205^5", U1*U1 < F("1.4205")**5)
check("1.9805^5 < 5.5200^2", F("1.9805")**5 < L2*L2)
check("5.5201^2 < 1.9806^5", U2*U2 < F("1.9806")**5)

# ---------- final kernel bound via my own interval Horner ----------
# K = (2/3) j1^a J0(c j1) + (1/3) j2^a J0(c j2), a=2/5, j1^a in [1.4204,1.4205], j2^a in [1.9805,1.9806]
# J0(c j1): q in [(c*L1)^2/4,(c*U1)^2/4];  p in [lo,hi]; J in [lo-E, hi+E]
p1lo, p1hi = interval_horner(pc, (c*L1)**2/4, (c*U1)**2/4)
J1lo, J1hi = p1lo - E, p1hi + E
p2lo, p2hi = interval_horner(pc, (c*L2)**2/4, (c*U2)**2/4)
J2lo, J2hi = p2lo - E, p2hi + E
print(f"J0(c*j1) in [{float(J1lo):.10f},{float(J1hi):.10f}]")
print(f"J0(c*j2) in [{float(J2lo):.10f},{float(J2hi):.10f}]")
# Upper bound of K: term1 = (2/3)*[1.4204,1.4205]*[J1lo,J1hi]; term2 = (1/3)*[1.9805,1.9806]*[J2lo,J2hi]
t1 = [F(2,3)*F("1.4204")*J1lo, F(2,3)*F("1.4205")*J1hi]
# J2hi < 0, so the interval endpoints reverse in the power factor.
check("second Bessel interval strictly negative", J2hi < 0)
t2 = [F(1,3)*F("1.9806")*J2lo, F(1,3)*F("1.9805")*J2hi]
Khi = t1[1] + t2[1]
Klo = t1[0] + t2[0]
print(f"K interval: [{float(Klo):.15f}, {float(Khi):.15f}]")
check("K < -1/500", Khi < F(-1,500), f"upper={Khi} = {float(Khi):.15f}")
check("K upper matches paper -653867/300000000", Khi <= F(-653867,300000000),
      f"paper bound={float(F(-653867,300000000)):.15f}")


# compare to candidate certificate json
cert = json.loads((Path(__file__).resolve().parents[2] / "bessel-exact-certificate.json").read_text())
certlo, certhi = map(F, cert["interior_witness"]["kernel_interval"])
check("corrected interval contained in parent exact interval", certlo <= Klo and Khi <= certhi)
print("corrected exact Klo =", Klo)
print("corrected exact Khi =", Khi)
def find_intervals(obj):
    out=[]
    def rec(o):
        if isinstance(o,dict):
            vals=[v for v in o.values() if isinstance(v,str) and "/" in v]
            if len(vals)>=2: out.append(o)
            for v in o.values(): rec(v)
        elif isinstance(o,list):
            for v in o: rec(v)
    rec(obj); return out
print("certificate keys:", list(cert.keys())[:20])

# ---------- independent mpmath cross-check ----------
try:
    import mpmath as mp
    mp.mp.dps = 60
    j1 = mp.findroot(mp.j0, 2.4); j2 = mp.findroot(mp.j0, 5.5)
    K = mp.mpf(2)/3 * j1**(mp.mpf(2)/5) * mp.j0(j1*mp.mpf(47)/50) \
      + mp.mpf(1)/3 * j2**(mp.mpf(2)/5) * mp.j0(j2*mp.mpf(47)/50)
    print("mpmath j1 =", mp.nstr(j1, 20))
    print("mpmath j2 =", mp.nstr(j2, 20))
    print("mpmath K(2/5,2,47/50) =", mp.nstr(K, 20))
    check("mpmath K < -1/500", K < mp.mpf(-1)/500, "high-precision independent value")
    check("my interval contains mpmath value", float(Klo) <= float(K) <= float(Khi))
    # zeros inside enclosures
    check("j1 in [2.4048,2.4049]", mp.mpf("2.4048") < j1 < mp.mpf("2.4049"))
    check("j2 in [5.5200,5.5201]", mp.mpf("5.5200") < j2 < mp.mpf("5.5201"))
except ImportError:
    print("mpmath unavailable; skipping float cross-check")

print("\nOVERALL:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
