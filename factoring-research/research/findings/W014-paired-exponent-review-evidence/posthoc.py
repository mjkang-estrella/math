"""POST-HOC corrections to certificate.py design errors (not preregistered).

The preregistered run (certificate-output.json, exit 1) is retained unchanged.
Diagnosed design errors: A7 filtered a by the GLOBAL gcd (dropping a with
a^2=d mod q, which are valid at p); A10 torus used z from a=0, i.e. z=-1 of
order 2; A11 chose blocks starting below sqrt(N), violating its own premise.
This script repeats only those checks with the corrected domain, plus A6/A8
with a nontrivial z. Run once: python3 -I posthoc.py > posthoc-output.json
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
    def __init__(self, m, d):
        self.m, self.d = m, d

    def mul(self, u, v):
        m, d = self.m, self.d
        return ((u[0] * v[0] + d * u[1] * v[1]) % m, (u[0] * v[1] + u[1] * v[0]) % m)

    def norm(self, u):
        return (u[0] * u[0] - self.d * u[1] * u[1]) % self.m

    def conj(self, u):
        return (u[0] % self.m, (-u[1]) % self.m)

    def inv(self, u):
        ni = pow(self.norm(u), -1, self.m)
        c = self.conj(u)
        return (c[0] * ni % self.m, c[1] * ni % self.m)

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


def order(R, z, bound):
    one = (1 % R.m, 0)
    for k in range(1, bound + 1):
        if bound % k == 0 and R.pow(z, k) == one:
            return k
    return None


def gpw(u, e, N):
    return pow(u, e, N) if e >= 0 else pow(pow(u, -1, N), -e, N)


out = {"assertions": {}, "failures": [], "cases": []}


def check(name, cond, detail=None):
    a = out["assertions"].setdefault(name, {"pass": 0, "fail": 0})
    a["pass" if cond else "fail"] += 1
    if not cond:
        out["failures"].append({"assertion": name, "detail": detail})


data = {}
for (r1, r2) in CASES:
    N = r1 * r2
    d = 2
    while jacobi(d, N) != -1:
        d += 1
    p, q = (r1, r2) if jacobi(d, r1) == -1 else (r2, r1)
    R, Rp, Rq = Ring(N, d), Ring(p, d), Ring(q, d)
    case = {"N": N, "p": p, "q": q, "d": d}
    if p <= 2000:
        img = {}
        for a in range(p):
            z = Rp.mul((a, 1), Rp.inv((a, p - 1)))
            img[z] = img.get(z, 0) + 1
        torus = sum(1 for x in range(p) for y in range(p) if (x * x - d * y * y) % p == 1)
        check("P-A7", torus == p + 1 and all(v == 1 for v in img.values())
              and len(img) == p and (1, 0) not in img, (N, len(img), torus))
    zs, ords = [], []
    for a in (1, 2, 3, 4, 5, 6):
        if math.gcd((a * a - d) % N, N) != 1:
            continue
        z = R.mul((a, 1), R.inv((a, N - 1)))
        op = order(Rp, (z[0] % p, z[1] % p), p + 1)
        oq = order(Rq, (z[0] % q, z[1] % q), q - 1)
        zs.append(z)
        ords.append({"a": a, "ord_p": op, "ord_q": oq})
        if len(zs) == 3:
            break
    case["z_orders"] = ords
    z = zs[0]
    u = 2
    T = (pow(u, N + 1, N), R.pow(z, N - 1))
    check("P-A6", T == (pow(u, p + q, N), R.mul(R.pow(z, p), R.pow(z, -q))), N)
    X = math.isqrt(N) + 1
    P = max(p, q)
    H, b = 8, 3
    check("P-A11-premise", X <= P < X + H, (N, X, P))
    Sx = lambda x: x + Fraction(N, x)
    check("P-A11", abs(Sx(X + H - 1) - Sx(X)) <= H - 1, (N, X))
    # A8 on the inert-p parameterization with nontrivial z
    Xp = p - 3
    a_sl = round(-b * q / p)
    q0 = round(Fraction(N, Xp))
    h = p - Xp
    e1 = b * q - b * q0 - a_sl * h
    lhs = (pow(T[0], b, N), R.pow(T[1], b))
    ue = b * Xp + b * q0 + b * h + a_sl * h + e1
    ze = b * Xp - b * q0 + b * h - a_sl * h - e1
    check("P-A8", lhs == (gpw(u, ue, N), R.pow(z, ze)), N)
    case["P-A8"] = {"X": Xp, "b": b, "a": a_sl, "q0": q0, "h": h, "e_prime": e1}
    data[N] = (p, q, R, zs)
    out["cases"].append(case)

surv = []
rng = range(-2, 3)
for a in rng:
    for b in rng:
        if a == 0 and b == 0:
            continue
        for al in rng:
            for be in rng:
                ok = all(R.pow(z, a * p + b * q) == R.pow(z, al + be * N)
                         for N, (p, q, R, zs) in data.items() for z in zs)
                if ok:
                    surv.append([a, b, al, be])
out["P-A10_torus_survivors"] = surv
check("P-A10_torus", len(surv) > 0 and all(b == -a and al == -a and be == a for a, b, al, be in surv), surv)
out["all_pass"] = not out["failures"]
json.dump(out, sys.stdout, indent=1, sort_keys=True)
print()
sys.exit(0 if out["all_pass"] else 1)
