"""W014 Card C fixed exact identity certificate (see preregistration.md).

Standard library only. Run once as: python3 -I certificate.py > certificate-output.json
"""
import json
import math
import sys
from fractions import Fraction

CASES = [(7, 11), (13, 17), (101, 103), (997, 1009), (10007, 10009)]


def jacobi(a, n):
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


class Ring:
    """(Z/mZ)[t]/(t^2-d); elements (x, y) = x + y t."""

    def __init__(self, m, d):
        self.m, self.d = m, d

    def mul(self, u, v):
        m, d = self.m, self.d
        return ((u[0] * v[0] + d * u[1] * v[1]) % m, (u[0] * v[1] + u[1] * v[0]) % m)

    def pow(self, u, e):
        if e < 0:
            u, e = self.inv(u), -e
        r = (1 % self.m, 0)
        while e:
            if e & 1:
                r = self.mul(r, u)
            u = self.mul(u, u)
            e >>= 1
        return r

    def norm(self, u):
        return (u[0] * u[0] - self.d * u[1] * u[1]) % self.m

    def conj(self, u):
        return (u[0] % self.m, (-u[1]) % self.m)

    def inv(self, u):
        n = self.norm(u)
        ni = pow(n, -1, self.m)
        c = self.conj(u)
        return (c[0] * ni % self.m, c[1] * ni % self.m)

    def red(self, u, m2):
        return (u[0] % m2, u[1] % m2)


def gpow(u, e, m):
    return pow(u, e, m)


results = {"cases": [], "controls": {}, "assertions": {}, "failures": []}


def check(name, cond, detail=None):
    a = results["assertions"].setdefault(name, {"pass": 0, "fail": 0})
    if cond:
        a["pass"] += 1
    else:
        a["fail"] += 1
        results["failures"].append({"assertion": name, "detail": detail})


zs_by_case = {}
for (r1, r2) in CASES:
    N = r1 * r2
    d = 2
    while jacobi(d, N) != -1:
        d += 1
    l1, l2 = jacobi(d, r1), jacobi(d, r2)
    check("A1", sorted((l1, l2)) == [-1, 1], (r1, r2, d, l1, l2))
    p, q = (r1, r2) if l1 == -1 else (r2, r1)
    R = Ring(N, d)
    S, D = p + q, p - q
    case = {"N": N, "d": d, "inert_p": p, "split_q": q, "S": S, "D": D}
    lim = min(N, 2000)
    gcd_values = {}
    zs = []
    cay_p = {}
    for a in range(lim):
        g = math.gcd((a * a - d) % N, N)
        gcd_values[g] = gcd_values.get(g, 0) + 1
        check("A2", g in (1, q), (N, a, g))
        if g != 1:
            continue
        z = R.mul((a, 1), R.inv((a, N - 1)))
        zs.append(z)
        check("A3_norm", R.norm(z) == 1, (N, a))
        Rp, Rq = Ring(p, d), Ring(q, d)
        zp, zq = R.red(z, p), R.red(z, q)
        check("A3_order_p", Rp.pow(zp, p + 1) == (1, 0), (N, a))
        check("A3_order_q", Rq.pow(zq, q - 1) == (1, 0), (N, a))
        check("A3_frob_p", Rp.pow(zp, p) == Rp.conj(zp), (N, a))
        lhs = R.pow(z, N - 1)
        check("A4", lhs == R.pow(z, p - q), (N, a))
        if p <= 2000 and a < p:
            cay_p[R.red(z, p)] = cay_p.get(R.red(z, p), 0) + 1
    case["gcd_counts"] = {str(k): v for k, v in sorted(gcd_values.items())}
    # opposite labeling record (not asserted)
    case["opposite_label_matches"] = sum(1 for z in zs if R.pow(z, N - 1) == R.pow(z, q - p))
    case["z_tested"] = len(zs)
    if p <= 2000:
        torus_p = 0
        for x in range(p):
            for y in range(p):
                if (x * x - d * y * y) % p == 1:
                    torus_p += 1
        injective = all(v == 1 for v in cay_p.values())
        misses_one = ((1, 0) not in cay_p) and len(cay_p) == torus_p - 1
        check("A7", injective and misses_one and torus_p == p + 1, (N, len(cay_p), torus_p))
        case["cayley"] = {"image": len(cay_p), "torus_order": torus_p}
    for u in (2, 3, 5):
        if math.gcd(u, N) != 1:
            continue
        check("A5", gpow(u, N + 1, N) == gpow(u, S, N), (N, u))
    z = zs[0]
    u = 2
    T = (gpow(u, N + 1, N), R.pow(z, N - 1))
    left = ((gpow(u, p, N) * gpow(u, q, N)) % N, R.mul(R.pow(z, p), R.pow(z, -q)))
    check("A6", left == T and S * S - D * D == 4 * N, N)

    def gp(e):  # g = (u, z)
        return (gpow(u, e, N) if e >= 0 else pow(pow(u, -1, N), -e, N), R.pow(z, e))

    def hp(e):  # hb = (u, z^-1)
        return (gpow(u, e, N) if e >= 0 else pow(pow(u, -1, N), -e, N), R.pow(z, -e))

    def pm(x, y):
        return (x[0] * y[0] % N, R.mul(x[1], y[1]))

    X, H, b = p - 3, 8, 3
    a_sl = round(-3 * q / p)
    q0 = round(Fraction(N, X))
    h = p - X
    e1 = b * q - b * q0 - a_sl * h
    Tb = (pow(T[0], b, N), R.pow(T[1], b))
    rhs = pm(pm(pm(gp(b * X), hp(b * q0)), pm(gp(b * h), hp(a_sl * h))), hp(e1))
    check("A8", Tb == rhs, (N, X, b, a_sl, q0, e1))
    case["A8_block"] = {"X": X, "H": H, "b": b, "a": a_sl, "q0": q0, "h": h, "e_prime": e1}
    # A11 using larger factor parameterization
    P = max(p, q)
    Xl = P - 3
    Sx = lambda x: x + Fraction(N, x)
    check("A11", Xl * Xl >= N and abs(Sx(Xl + H - 1) - Sx(Xl)) <= H - 1, (N, Xl))
    # A9 full unit group digits at inert prime
    Rp = Ring(p, d)
    for w in ((1, 2), (3, 1)):
        wp = Rp.red(w, p)
        check("A9_frob", Rp.pow(wp, p) == Rp.conj(wp), (N, w))
        for e0 in range(-2, 3):
            for e1d in range(-2, 3):
                check("A9_digit", Rp.pow(wp, e0 + e1d * p)
                      == Rp.mul(Rp.pow(wp, e0), Rp.pow(Rp.conj(wp), e1d)), (N, w, e0, e1d))
    zs_by_case[N] = (p, q, R, z)
    results["cases"].append(case)

# A10 affine classification across all five cases
g_surv, t_surv = [], []
rng = range(-2, 3)
for a in rng:
    for b in rng:
        if a == 0 and b == 0:
            continue
        for al in rng:
            for be in rng:
                okg = okt = True
                for N, (p, q, R, z) in zs_by_case.items():
                    x, y = a * p + b * q, al + be * N
                    for u in (2, 3):
                        if pow(u, x, N) != pow(u, y, N) if x >= 0 and y >= 0 else \
                                pow(pow(u, -1, N) if x < 0 else u, abs(x), N) != pow(pow(u, -1, N) if y < 0 else u, abs(y), N):
                            okg = False
                    if R.pow(z, x) != R.pow(z, y):
                        okt = False
                if okg:
                    g_surv.append([a, b, al, be])
                if okt:
                    t_surv.append([a, b, al, be])
results["A10_G_survivors"] = g_surv
results["A10_torus_survivors"] = t_surv
check("A10_G_expected", all(a == b == al == be for a, b, al, be in g_surv) and len(g_surv) > 0, g_surv)
check("A10_torus_expected", all(b == -a and al == -a and be == a for a, b, al, be in t_surv) and len(t_surv) > 0, t_surv)

# Non-semiprime controls
results["controls"]["N121_jacobi_minus_one_count"] = sum(1 for dd in range(1, 121) if jacobi(dd, 121) == -1)
splits = [(a, 105 // a) for a in range(2, 11) if 105 % a == 0 and a < 105 // a]
results["controls"]["N105_u2_identity"] = {f"{a}*{b}": pow(2, 106, 105) == pow(2, a + b, 105) for a, b in splits}

results["all_asserted_pass"] = not results["failures"]
json.dump(results, sys.stdout, indent=1, sort_keys=True)
print()
sys.exit(0 if results["all_asserted_pass"] else 1)
