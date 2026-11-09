"""Independent adversarial checker for the root-mittag-modulus-r12 candidate.

Deliberately different routes from the root's check_identities.py /
check_finite_product.py:
  A. half-normal cf (3) by direct 1D quadrature of the density (root: moments/ODE)
  B. angular kernel (2) verified via 2D rectangle quadrature (root: 1D angular quad)
  C. E Y_k^q by direct integration of the literal two-part law for IRRATIONAL beta
     (root used rational beta closed forms / gamma closed forms)
  D. finite-difference signs of F_N = |M_N(i sqrt t)|^2 computed PURELY by series,
     never invoking the angular kernel (tests steps 3-4 independently)
  E. sign of (-1)^k f_a^(k)(t) for the LITERAL source function via the reviewer's
     own coefficient formula c_j = sum_{j'=-j}^{j} (-1)^j' /
     [Gamma(a(j+j')+1) Gamma(a(j-j')+1)], with cancellation-safety accounting
     (root only checked the Taylor coefficients c_j > 0, a weaker necessary condition)
  F. Euler Gamma limit (5) and monotonicity (6) at irrational beta via literal products
Resource-bounded: mpmath only, dps<=120, no large enumerations.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80
OUT = {}
fail = []


def check(name, cond, detail=""):
    if not cond:
        fail.append((name, detail))
        print("FAIL", name, detail)
    return cond


# ---------- A. half-normal cf by direct quadrature ----------
rowsA = []
for z in ["0.3", "1.7", "4.0"]:
    z = mp.mpf(z)
    direct = mp.quad(lambda x: mp.cos(z * x) * mp.e ** (-x * x / 4) / mp.sqrt(mp.pi), [0, mp.inf]) \
        + 1j * mp.quad(lambda x: mp.sin(z * x) * mp.e ** (-x * x / 4) / mp.sqrt(mp.pi), [0, mp.inf])
    closed = mp.e ** (-z ** 2) * (1 + 1j * mp.erfi(z))
    err = abs(direct - closed)
    check("A cf half-normal z=" + z.__str__(), err < mp.mpf("1e-50"), mp.nstr(err, 5))
    rowsA.append({"z": str(z), "abs_err": mp.nstr(err, 5)})
OUT["A_half_normal_cf"] = rowsA

# ---------- B. kernel via 2D rectangle quadrature (unequal v,w; wide t) ----------
rowsB = []
for vs, ws in [("0.2", "3.0"), ("4.0", "0.03"), ("1", "1"), ("7.0", "2.0"), ("0.01", "0.02")]:
    v, w = mp.mpf(vs), mp.mpf(ws)
    s = v + w
    for ts in ["0.001", "0.4", "5", "80"]:
        t = mp.mpf(ts)
        rect = mp.e ** (-s * t) + (4 * t / mp.pi) * mp.quad(
            lambda x: mp.quad(lambda y: mp.e ** (-t * (s - x * x - y * y)), [0, mp.sqrt(w)]),
            [0, mp.sqrt(v)])
        closed = mp.e ** (-s * t) * (1 + mp.erfi(mp.sqrt(v * t)) * mp.erfi(mp.sqrt(w * t)))
        err = abs(rect - closed) / abs(closed)
        check("B kernel 2D v=%s w=%s t=%s" % (vs, ws, ts), err < mp.mpf("1e-40"), mp.nstr(err, 5))
        rowsB.append({"v": vs, "w": ws, "t": ts, "rel_err": mp.nstr(err, 5)})
# L >= 0 on a theta grid, unequal scales
for vs, ws in [("0.2", "3.0"), ("7.0", "2.0")]:
    v, w = mp.mpf(vs), mp.mpf(ws)
    s = v + w
    for i in range(1, 200):
        th = mp.pi * i / 400
        R2 = min(v / mp.cos(th) ** 2, w / mp.sin(th) ** 2)
        check("B L>=0", R2 <= s + mp.mpf("1e-40"), "%s %s %s" % (vs, ws, i))
OUT["B_kernel_2D"] = rowsB

def R_N(q, N, beta):
    q = mp.mpf(q)
    return mp.mpf(N) ** ((1 - beta) * q) * mp.fprod((k + beta * q) / (k + q) for k in range(1, N + 1))


# ---------- C. moment of the literal two-part law, irrational beta ----------
beta_irr = mp.mpf("0.413753917")  # deliberately irrational-ish, not a small-denominator rational
rowsC = []
for k in [1, 3, 9]:
    for qs in ["0", "0.5", "2.5", "7"]:
        q = mp.mpf(qs)
        lit = beta_irr * 1 + (1 - beta_irr) * mp.quad(lambda y: k * y ** (k - 1) * y ** q, [0, 1])
        closed = (k + beta_irr * q) / (k + q)
        err = abs(lit - closed) / closed
        check("C E Y^q k=%d q=%s" % (k, qs), err < mp.mpf("1e-40"), mp.nstr(err, 5))
        rowsC.append({"k": k, "q": qs, "rel_err": mp.nstr(err, 5)})
OUT["C_two_part_law_moments"] = rowsC

# ---------- F. Euler limit + monotonicity at irrational beta, literal products ----------
rowsF = []
for qs in ["0.5", "2", "6.5"]:
    q = mp.mpf(qs)
    limit = mp.gamma(1 + q) / mp.gamma(1 + beta_irr * q)
    prev = mp.mpf(0)
    for N in [1, 2, 5, 20, 100, 1000]:
        rn = R_N(q, N, beta_irr)
        if prev:
            check("F monotone N=%d q=%s" % (N, qs), prev <= rn * (1 + mp.mpf("1e-50")))
        check("F upper bound N=%d q=%s" % (N, qs), rn <= limit * (1 + mp.mpf("1e-50")))
        prev = rn
    rn = R_N(q, 4000, beta_irr)
    rel = abs(rn / limit - 1)
    check("F euler conv q=%s" % qs, rel < mp.mpf("5e-3"), mp.nstr(rel, 5))
    rowsF.append({"q": qs, "N=4000 rel err to limit": mp.nstr(rel, 5)})
OUT["F_euler_limit_irrational"] = rowsF

# ---------- D. finite-difference signs of series-defined F_N (no kernel used) ----------
def M_N_iz(mpf_t, beta, N):
    """M_N(i sqrt t) = sum_n (i sqrt t)^n R_N(n/2)/Gamma(1+n/2)."""
    z = 1j * mp.sqrt(mpf_t)
    s = mp.mpc(0)
    n = 0
    while True:
        term = z ** n * R_N(n / 2, N, beta) / mp.gamma(1 + n / 2)
        s += term
        n += 1
        if n > 8 and abs(term) < mp.mpf("1e-70") * max(1, abs(s)):
            break
        if n > 20000:
            raise RuntimeError("series stall")
    return s


def F_N(t, beta, N):
    m = M_N_iz(t, beta, N)
    return abs(m) ** 2


rowsD = []
for bs, Ns in [("0.9", 3), ("0.413753917", 7), ("0.1", 12), ("0.02", 25)]:
    beta = mp.mpf(bs)
    for ts, hs in [("0.05", "0.3"), ("1.0", "0.7"), ("3.0", "1.5")]:
        t, h = mp.mpf(ts), mp.mpf(hs)
        for kk in [1, 2, 3, 5]:
            fd = sum((-1) ** (kk - j) * mp.binomial(kk, j) * F_N(t + j * h, beta, Ns) for j in range(kk + 1))
            sign_ok = (-1) ** kk * fd >= -mp.mpf("1e-55") * max(1, abs(fd))
            check("D fd-sign beta=%s N=%d t=%s h=%s k=%d" % (bs, Ns, ts, hs, kk), sign_ok,
                  mp.nstr(fd, 8))
            rowsD.append({"beta": bs, "N": Ns, "t": ts, "h": hs, "k": kk,
                          "value": mp.nstr((-1) ** kk * fd, 12)})
OUT["D_series_fd_signs"] = {"rows": rowsD[:12], "n_checked": len(rowsD)}

# ---------- E. derivative signs of the literal f_a via reviewer coefficient formula ----------
# c_j = coefficient of t^j in E_a(i sqrt t) E_a(-i sqrt t) (reviewer's own derivation,
# cross-checked in G). f^(k)(t) = sum_{j>=k} c_j (j)_k t^(j-k), an exact entire-series
# identity. Terms can be enormous (e.g. ~1e352 at a=0.25,t=20) while the sum is O(1):
# precision is therefore set adaptively from a float lgamma estimate of the max term,
# and J is extended until the tail is provably negligible; infeasible cases are skipped
# and reported rather than silently mis-evaluated.
import math


def est_digits_and_J(a, t, k):
    """Float estimate of log10(max term) and required truncation J for the derivative sum."""
    a, t, k = float(a), float(t), int(k)

    def logterm(j):
        return j * math.log(t) - 2 * math.lgamma(a * j + 1) + (sum(math.log(j - i) for i in range(k)) if k else 0)

    # scan for max in nats, then convert to digits
    best = -1e18
    jstar = 1
    j = k
    while j <= 200000:
        lt = j * math.log(t) - 2 * math.lgamma(a * j + 1)
        if k:
            lt += sum(math.log(j - i) for i in range(k))
        if lt > best:
            best = lt
            jstar = j
        j = max(j + 1, int(1.02 * j) + 1) if j > 100 else j + 1
    digits = best / math.log(10) if best > 0 else 0
    # extend J until term below max - 70 nats*ln10
    target = best - 70 * math.log(10) if best > 0 else -161
    J = 200000  # default: infeasible unless break
    j = jstar
    while j < 200000:
        j += max(1, j // 50)
        lt = j * math.log(t) - 2 * math.lgamma(a * j + 1) + (sum(math.log(j - i) for i in range(k)) if k else 0)
        if lt < target:
            J = j
            break
    return digits, min(J, 200000), jstar


def deriv_sign(a, t, k, J, dps):
    """(-1)^k f^(k)(t) via exact entire-series identity with gamma table."""
    mp.mp.dps = dps
    a, t = mp.mpf(a), mp.mpf(t)
    gam = [mp.gamma(a * m + 1) for m in range(2 * J + 2)]  # Gamma(a*m+1) table

    def coeff_c(j):
        s = mp.mpf(0)
        for jp in range(-j, j + 1):
            s += (-1) ** jp / (gam[j + jp] * gam[j - jp])
        return s

    total = mp.mpf(0)
    maxterm = mp.mpf(0)
    for j in range(k, J + 1):
        falling = mp.mpf(1)
        for i in range(k):
            falling *= (j - i)
        term = coeff_c(j) * falling * t ** (j - k)
        maxterm = max(maxterm, abs(term))
        total += term
    return (-1) ** k * total, maxterm


grids = {
    "0.5": ["0.001", "0.5", "5", "50", "150"],
    "0.45": ["0.001", "0.5", "5", "20"],
    "0.35": ["0.001", "0.5", "2", "6", "20"],
    "0.25": ["0.001", "1", "5", "10", "20"],
    "0.15": ["0.001", "0.5", "1.5", "3"],
    "0.05": ["0.001", "0.5", "1.2"],
    "0.02": ["0.001", "0.7", "1.05"],
}
rowsE = []
skipped = []
OPS_CAP = 6_000_000
for as_, ts_list in grids.items():
    a = mp.mpf(as_)
    for ts in ts_list:
        t = mp.mpf(ts)
        for kk in [1, 2, 3, 4, 6, 8]:
            digits, J, jstar = est_digits_and_J(as_, ts, kk)
            ops = J * J
            if ops > OPS_CAP or digits > 500:
                skipped.append({"a": as_, "t": ts, "k": kk, "reason": "ops=%d est_digits=%.0f" % (ops, digits)})
                continue
            dps = int(90 + digits + 20)
            val, maxterm = deriv_sign(as_, ts, kk, J, dps)
            margin = dps - mp.log10(max(maxterm, mp.mpf("1e-300")))
            check("E deriv sign a=%s t=%s k=%d" % (as_, ts, kk),
                  val >= -mp.mpf("1e-30") * max(1, abs(val)), "value=%s" % mp.nstr(val, 8))
            rowsE.append({"a": as_, "t": ts, "k": kk, "(-1)^k f^(k)(t)": mp.nstr(val, 12),
                          "dps": dps, "J": J, "jstar": jstar,
                          "cancellation_margin_digits": mp.nstr(margin, 4)})
OUT["E_derivative_signs_literal_f"] = {"rows": rowsE[:16], "n_checked": len(rowsE), "skipped": skipped[:20]}

# a = 1/2 endpoint: independent closed form f = e^{-2t}(1+erfi(sqrt t)^2), mpmath diff
def f_half(t):
    return mp.e ** (-2 * t) * (1 + mp.erfi(mp.sqrt(t)) ** 2)


rowsE2 = []
for ts in ["0.05", "1", "10", "60"]:
    t = mp.mpf(ts)
    for kk in [1, 2, 3, 4]:
        d = mp.diff(f_half, t, kk)
        val = (-1) ** kk * d
        check("E2 endpoint a=1/2 closed-form t=%s k=%d" % (ts, kk), val >= -mp.mpf("1e-40") * max(1, abs(val)),
              mp.nstr(val, 8))
        rowsE2.append({"t": ts, "k": kk, "(-1)^k f^(k)": mp.nstr(val, 10)})
OUT["E2_half_closed_form"] = rowsE2

# ---------- G. cross-check coefficient formula against direct series product ----------
mp.mp.dps = 80
a = mp.mpf("0.3")
for j in [0, 1, 2, 5]:
    lhs = sum((-1) ** jp / (mp.gamma(a * (j + jp) + 1) * mp.gamma(a * (j - jp) + 1))
              for jp in range(-j, j + 1))
    # direct: coefficient of t^j in E_a(i sqrt t) E_a(-i sqrt t)
    s = mp.mpf(0)
    for n in range(0, 2 * j + 1):
        m = 2 * j - n
        if (n - m) % 2 == 0:
            s += (1j) ** (n - m) / (mp.gamma(a * n + 1) * mp.gamma(a * m + 1))
    err = abs(lhs - s)
    check("G coeff formula j=%d" % j, err < mp.mpf("1e-60"), mp.nstr(err, 5))
OUT["G_coeff_crosscheck"] = "PASS"

OUT["status"] = "PASS all independent diagnostics" if not fail else "FAILURES: %d" % len(fail)
OUT["failures"] = fail[:20]
p = Path(__file__).resolve().parent / "independent-checks.json"
p.write_text(json.dumps(OUT, indent=1) + "\n")
print(OUT["status"], "| A:%d B:%d C:%d D:%d E:%d F:%d checks" % (
    len(rowsA), len(rowsB), len(rowsC), len(rowsD), len(rowsE) + len(rowsE2), len(rowsF)))
