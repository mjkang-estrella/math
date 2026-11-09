"""Exact certificates for the W009 geometric-escape review; not a factoring candidate.

Part S: symbolic polynomial identities over Q (stdlib Fractions).
Part F: exact finite certificates on a FIXED, preregistered list of tiny
fields/curves (constants below). No parameter search, prime sweep, depth
sweep, timing, or solver run. Run from the factoring-research root; writes
only research/findings/W009-escape-review-check.json.
"""

from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import json


class Poly:
    """Sparse multivariate polynomial over Q; keys are sorted (var, exp) tuples."""

    def __init__(self, terms=None):
        if terms is None:
            terms = {}
        elif not isinstance(terms, dict):
            terms = {(): Fraction(terms)}
        self.t = {k: Fraction(v) for k, v in terms.items() if v}

    @staticmethod
    def var(name):
        return Poly({((name, 1),): 1})

    @staticmethod
    def c(x):
        return x if isinstance(x, Poly) else Poly(x)

    def __add__(self, o):
        r = dict(self.t)
        for k, v in Poly.c(o).t.items():
            r[k] = r.get(k, 0) + v
        return Poly(r)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()})

    def __sub__(self, o):
        return self + -Poly.c(o)

    def __rsub__(self, o):
        return Poly.c(o) - self

    def __mul__(self, o):
        r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in Poly.c(o).t.items():
                d = dict(k1)
                for n, e in k2:
                    d[n] = d.get(n, 0) + e
                k = tuple(sorted(d.items()))
                r[k] = r.get(k, 0) + v1 * v2
        return Poly(r)

    __rmul__ = __mul__

    def __pow__(self, e):
        r = Poly(1)
        for _ in range(e):
            r = r * self
        return r

    def zero(self):
        return not self.t


V = Poly.var
checks = []


def record(name, ok, detail=None):
    entry = {"name": name, "passed": bool(ok)}
    if detail is not None:
        entry["detail"] = detail
    checks.append(entry)
    assert ok, (name, detail)


def identity(name, left, right):
    record(name, (Poly.c(left) - Poly.c(right)).zero())


# ---------------------------------------------------------------- Part S
X, Y, A, B, r, s, u, v, a, U, W, c, rho = (
    V(n) for n in ["X", "Y", "A", "B", "r", "s", "u", "v", "a", "U", "W", "c", "rho"]
)
Vv = V("V")

# S1. Coalesced fold on a carried square: projective coordinates agree exactly.
Up, Vp, y = U**2, Vv**2, a**2
identity("S1 G_(a^2)([U^2:V^2]) numerator = (U^2-a^2V^2)^2", (Up - y * Vp) ** 2, (U**2 - a**2 * Vv**2) ** 2)
identity("S1 G_(a^2)([U^2:V^2]) denominator = (UV)^2", Up * Vp, (U * Vv) ** 2)
identity("S1 odd fold (U-aV)(U+aV) = U^2-a^2V^2", (U - a * Vv) * (U + a * Vv), U**2 - a**2 * Vv**2)

# S2. 2-isogeny with kernel (0,0) on Y^2 = X^3+AX^2+BX.
f = X**3 + A * X**2 + B * X
identity("S2 X(X-r)(X-s) = X^3+AX^2+BX at A=-(r+s),B=rs",
         X * (X - r) * (X - s), X**3 - (r + s) * X**2 + r * s * X)
Wn = X**2 + A * X + B  # X' = Wn / X
# Y'^2 X^3 with Y'=Y(X^2-B)/X^2 and Y^2=f, versus target(X') X^3.
lhs = f * (X**2 - B) ** 2 * X  # = Y'^2 * X^5 ... normalized below
rhs = (Wn**3 - 2 * A * Wn**2 * X + (A**2 - 4 * B) * Wn * X**2) * X**2
identity("S2 target E': Y'^2 = X'^3-2AX'^2+(A^2-4B)X' (cleared by X^5)", lhs, rhs)
identity("S2 target discriminant factors: (2A)^2-4(A^2-4B) = 16B", (2 * A) ** 2 - 4 * (A**2 - 4 * B), 16 * B)
identity("S2 A^2-4B = (r-s)^2 at A=-(r+s),B=rs", (r + s) ** 2 - 4 * r * s, (r - s) ** 2)
# Target roots with r=u^2, s=v^2: X'^2-2AX'+A^2-4B = (X'+(u-v)^2)(X'+(u+v)^2)
Au, Bu = -(u**2 + v**2), u**2 * v**2
identity("S2 target roots -(u-v)^2,-(u+v)^2 when r=u^2,s=v^2",
         X**2 - 2 * Au * X + Au**2 - 4 * Bu, (X + (u - v) ** 2) * (X + (u + v) ** 2))
identity("S2 r'*s' = (u^2-v^2)^2", (u - v) ** 2 * (u + v) ** 2, (u**2 - v**2) ** 2)
identity("S2 r'-s' = 4uv", (u + v) ** 2 - (u - v) ** 2, 4 * u * v)

# S3. Doubling x-map: tangent-line formula equals (X^2-B)^2/(4f).
lam_num = 3 * X**2 + 2 * A * X + B
identity("S3 x(2Q) = (X^2-B)^2/(4Y^2) via tangent law",
         lam_num**2 - 4 * f * (A + 2 * X), (X**2 - B) ** 2)

# S4. Two folds, projective and exact, using only (sum, product) of target roots.
U1 = (U - r * Vv) * (U - s * Vv)
V1 = U * Vv
sum2, prod2 = -2 * (r + s), (r - s) ** 2  # r'+s' and r'*s' WITHOUT square roots
U2 = U1**2 - sum2 * U1 * V1 + prod2 * V1**2
V2 = U1 * V1
identity("S4 second-fold numerator = (U^2-rsV^2)^2 using only r'+s',r's'", U2, (U**2 - r * s * Vv**2) ** 2)
identity("S4 second-fold denominator = UV(U-rV)(U-sV)", V2, U * Vv * (U - r * Vv) * (U - s * Vv))
# Same with the explicit anchors r'=-(u-v)^2, s'=-(u+v)^2.
ru, su = u**2, v**2
U1u = (U - ru * Vv) * (U - su * Vv)
V1u = U * Vv
U2u = (U1u + (u - v) ** 2 * V1u) * (U1u + (u + v) ** 2 * V1u)
identity("S4 explicit-anchor second fold numerator", U2u, (U**2 - u**2 * v**2 * Vv**2) ** 2)
# Hence two folds = 4*x([2]Q): (X^2-B)^2/(X(X-r)(X-s)) = 4*(X^2-B)^2/(4f).
# Scaling: dual-of-dual coefficients and F_(4r,4s)(4z) = 4 F_(r,s)(z).
A1, B1 = -2 * A, A**2 - 4 * B
identity("S4 A''=-2A'=4A", -2 * A1, 4 * A)
identity("S4 B''=A'^2-4B'=16B", A1**2 - 4 * B1, 16 * B)
identity("S4 iso (X,Y)->(4X,8Y): 64f(X) = (4X)^3+4A(4X)^2+16B(4X)",
         64 * f, (4 * X) ** 3 + 4 * A * (4 * X) ** 2 + 16 * B * (4 * X))
identity("S4 F_(4r,4s)(4z) = 4F_(r,s)(z) (cleared)",
         (4 * X - 4 * r) * (4 * X - 4 * s) * X, 4 * (X - r) * (X - s) * (4 * X))

# S5. Explicit family carries a rational 4-torsion point on E'.
X0 = u**2 - v**2
identity("S5 R=(u^2-v^2, 2u(u^2-v^2)) lies on E'", X0 * (X0 + (u - v) ** 2) * (X0 + (u + v) ** 2),
         (2 * u * X0) ** 2)
identity("S5 x(2R)=0 since X0^2 = r's'", X0**2, (u - v) ** 2 * (u + v) ** 2)

# S6. Kernel (r,0): translated cubic and B_r.
X1 = V("X1")
identity("S6 f(X1+r) = X1(X1+r)(X1+r-s)", (X1 + r) * (X1 + r - r) * (X1 + r - s), X1 * (X1 + r) * (X1 + r - s))
identity("S6 B_r = (-r)(s-r) = r(r-s)", (-r) * (s - r), r * (r - s))

# S7. Odd/Newton-form fold z+c/z is the kernel-(0,0) 2-isogeny of Y^2=X^3+cX.
#     Schedule c -> -4c is elliptic doubling; c -> 4c is the torus frame.
Fz_num, Fz_den = X**2 + c, X  # F_c(X)
# second fold with parameter -4c:  (Fz^2 - 4c)/Fz
num2 = Fz_num**2 - 4 * c * Fz_den**2
den2 = Fz_num * Fz_den
identity("S7 (c then -4c) numerator = (X^2-c)^2", num2, (X**2 - c) ** 2)
identity("S7 (c then -4c) denominator = X(X^2+c) = f for Y^2=X^3+cX", den2, X**3 + c * X)
# torus: (F(z)-2rho)/(F(z)+2rho) = ((z-rho)/(z+rho))^2 with c=rho^2
Fr = X**2 + rho**2
identity("S7 torus frame: (F-2rho)(z+rho)^2 = (F+2rho)(z-rho)^2 (cleared by z)",
         (Fr - 2 * rho * X) * (X + rho) ** 2, (Fr + 2 * rho * X) * (X - rho) ** 2)
# odd fold z-a^2/z: Y^2 = X^3-a^2X is the quadratic twist by a of Y^2=X^3-X
Yc = V("Yc")
identity("S7 x=aX,y=a^2Y: y^2-(x^3-a^2x) = a^3(aY^2-(X^3-X))",
         (a**2 * Yc) ** 2 - ((a * X) ** 3 - a**2 * (a * X)), a**3 * (a * Yc**2 - (X**3 - X)))


# ---------------------------------------------------------------- Part F helpers
def legendre(x, p):
    x %= p
    if x == 0:
        return 0
    return 1 if pow(x, (p - 1) // 2, p) == 1 else -1


def nonsquare(p):
    return next(d for d in range(2, p) if legendre(d, p) == -1)


class Fp2:
    """F_p[t]/(t^2-d), d a nonsquare."""

    def __init__(self, p, d, x, y=0):
        self.p, self.d, self.x, self.y = p, d, x % p, y % p

    def __add__(self, o):
        return Fp2(self.p, self.d, self.x + o.x, self.y + o.y)

    def __sub__(self, o):
        return Fp2(self.p, self.d, self.x - o.x, self.y - o.y)

    def __mul__(self, o):
        p, d = self.p, self.d
        return Fp2(p, d, self.x * o.x + d * self.y * o.y, self.x * o.y + self.y * o.x)

    def inv(self):
        p, d = self.p, self.d
        n = (self.x * self.x - d * self.y * self.y) % p
        ni = pow(n, p - 2, p)
        return Fp2(p, d, self.x * ni, -self.y * ni)

    def iszero(self):
        return self.x == 0 and self.y == 0

    def __eq__(self, o):
        return self.x == o.x and self.y == o.y


def ec_add(P, Q, Acoef, Bcoef, K):
    """Affine group law on y^2=x^3+Ax^2+Bx over field elements of type K; None = O."""
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2:
        if (y1 + y2).iszero():
            return None
        lam = (K(3) * x1 * x1 + K(2) * Acoef * x1 + Bcoef) * (K(2) * y1).inv()
    else:
        lam = (y2 - y1) * (x2 - x1).inv()
    x3 = lam * lam - Acoef - x1 - x2
    y3 = lam * (x1 - x3) - y1
    return (x3, y3)


def ec_mul(m, P, Acoef, Bcoef, K):
    R = None
    Q = P
    while m:
        if m & 1:
            R = ec_add(R, Q, Acoef, Bcoef, K)
        Q = ec_add(Q, Q, Acoef, Bcoef, K)
        m >>= 1
    return R


def sqrt_fp2(z, p, d):
    """Square root in F_{p^2} of an element of F_p (exists always). Brute force for tiny p."""
    z %= p
    for x0 in range(p):
        for y0 in range(p):
            w = Fp2(p, d, x0, y0)
            if (w * w) == Fp2(p, d, z):
                return w
    raise AssertionError("no root")


def rational_points(p, Ac, Bc):
    pts = [None]
    for x0 in range(p):
        rhs = (x0**3 + Ac * x0 * x0 + Bc * x0) % p
        for y0 in range(p):
            if (y0 * y0 - rhs) % p == 0:
                pts.append((x0, y0))
    return pts


class Fp:
    def __init__(self, p, x):
        self.p, self.x = p, x % p

    def __add__(self, o):
        return Fp(self.p, self.x + o.x)

    def __sub__(self, o):
        return Fp(self.p, self.x - o.x)

    def __mul__(self, o):
        return Fp(self.p, self.x * o.x)

    def inv(self):
        return Fp(self.p, pow(self.x, self.p - 2, self.p))

    def iszero(self):
        return self.x == 0

    def __eq__(self, o):
        return self.x == o.x


def kill_count(p, Ac, Bc, m):
    """|E(F_p)[m]| for y^2=x^3+Ac x^2+Bc x."""
    K = lambda z: Fp(p, z)
    n = 0
    for P in rational_points(p, Ac, Bc):
        PP = None if P is None else (K(P[0]), K(P[1]))
        if ec_mul(m, PP, K(Ac), K(Bc), K) is None:
            n += 1
    return n


def twist_coeffs(p, Ac, Bc, d):
    # d*Y^2 = X^3+AX^2+BX  ~  Y'^2 = X'^3 + dA X'^2 + d^2 B X'  via X'=dX, Y'=d^2Y
    return (d * Ac) % p, (d * d * Bc) % p


def x_poles_via_fp2(p, Ac, Bc, m):
    """#{x in P^1(F_p): [m]Q=O for a geometric lift Q}, computed in F_{p^2}, independent of twists."""
    d = nonsquare(p)
    K = lambda z: Fp2(p, d, z)
    count = 1  # x = infinity: Q = O
    for x0 in range(p):
        rhs = (x0**3 + Ac * x0 * x0 + Bc * x0) % p
        Q = (K(x0), sqrt_fp2(rhs, p, d))
        if ec_mul(m, Q, K(Ac), K(Bc), K) is None:
            count += 1
    return count


# ---------------------------------------------------------------- Part F
# Preregistered fixed instances (chosen before running; never searched).
CURVES_F1 = [  # (p, A, B, label)
    (11, -(4 + 9) % 11, (4 * 9) % 11, "r=u^2=4,s=v^2=9 (full 2-torsion)"),
    (13, -(4 + 9) % 13, (4 * 9) % 13, "r=4,s=9 (full 2-torsion)"),
    (13, 1, 3, "A=1,B=3 (A^2-4B=-11 nonsquare mod 13: one rational 2-torsion pt)"),
]
f1 = []
for p, Ac, Bc, label in CURVES_F1:
    assert Bc % p and (Ac * Ac - 4 * Bc) % p
    d = nonsquare(p)
    At, Bt = twist_coeffs(p, Ac, Bc, d)
    for m in range(1, 2 * p + 4):
        am, bm = kill_count(p, Ac, Bc, m), kill_count(p, At, Bt, m)
        direct = x_poles_via_fp2(p, Ac, Bc, m)
        record(f"F1 (5) p={p} {label} m={m}", (am + bm) % 2 == 0 and direct == (am + bm) // 2,
               {"a_m": am, "b_m": bm, "direct": direct})
    f1.append({"p": p, "A": Ac, "B": Bc, "label": label, "m_range": [1, 2 * p + 3]})


def fold_chain_first_pole(p, x0, schedule):
    """Projective circuit [U:V] -> [U^2 - S U V + P V^2 : U V]; returns first stage with V=0."""
    Uc, Vc = x0 % p, 1
    for j, (S, P) in enumerate(schedule, start=1):
        Uc, Vc = (Uc * Uc - S * Uc * Vc + P * Vc * Vc) % p, (Uc * Vc) % p
        assert Uc or Vc, "basepoint"
        if Vc == 0:
            return j, None
    return None, (Uc, Vc)


def coherent_schedule(rr, ss, stages, p):
    """(sum, product) of anchors; odd stages use 4^j (r, s); even use 4^j (r', s') via sum/product only."""
    sched = []
    for j in range(stages):
        k = j // 2
        if j % 2 == 0:
            sched.append(((4**k) * (rr + ss) % p, (16**k) * rr * ss % p))
        else:
            sched.append(((4**k) * (-2) * (rr + ss) % p, (16**k) * (rr - ss) ** 2 % p))
    return sched


def subgroup_preimage_size(p, Ac, Bc, k, T0):
    """|{Q in E(F_p): [2^k]Q in {O, T0}}|."""
    K = lambda z: Fp(p, z)
    n = 0
    for P in rational_points(p, Ac, Bc):
        PP = None if P is None else (K(P[0]), K(P[1]))
        R = ec_mul(2**k, PP, K(Ac), K(Bc), K)
        if R is None or (R[0].x == T0[0] and R[1].x == T0[1]):
            n += 1
    return n


CHAIN_F2 = [  # (p, r, s, label)
    (13, 4, 9, "explicit family u=2,v=3"),
    (13, 2, 5, "r*s=10 nonsquare mod 13: dual cycle needs no root"),
    (11, 3, 7, "r*s=21=10 nonsquare mod 11"),
]
DEPTH = 8  # folds, i.e. doubling depth 4
f2 = []
for p, rr, ss, label in CHAIN_F2:
    Ac, Bc = -(rr + ss) % p, rr * ss % p
    d = nonsquare(p)
    At, Bt = twist_coeffs(p, Ac, Bc, d)
    sched = coherent_schedule(rr, ss, DEPTH, p)
    first = [fold_chain_first_pole(p, x0, sched)[0] for x0 in range(p)]
    # exact functional identity: even stage value = 4^k x([2^k]Q), checked in F_{p^2}
    K = lambda z: Fp2(p, d, z)
    for x0 in range(p):
        rhs = (x0**3 + Ac * x0 * x0 + Bc * x0) % p
        Q = (K(x0), sqrt_fp2(rhs, p, d))
        for k in range(1, DEPTH // 2 + 1):
            fp, out = fold_chain_first_pole(p, x0, sched[: 2 * k])
            R = ec_mul(2**k, Q, K(Ac), K(Bc), K)
            if fp is not None:
                ok = R is None
            else:
                Uc, Vc = out
                ok = R is not None and R[0].y == 0 and (Uc - (4**k) * R[0].x * Vc) % p == 0
            record(f"F2 (4) p={p} {label} x={x0} k={k}: P_2k = 4^k x([2^k]Q)", ok)
    stages = []
    for j in range(1, DEPTH + 1):
        cnt = sum(1 for t in first if t is not None and t <= j)
        k = j // 2
        if j % 2 == 0:
            pred = (kill_count(p, Ac, Bc, 2**k) + kill_count(p, At, Bt, 2**k)) // 2 - 1
        else:
            sE = subgroup_preimage_size(p, Ac, Bc, k, (0, 0))
            sT = subgroup_preimage_size(p, At, Bt, k, (0, 0))
            pred = (sE + sT) // 2 - 1
        record(f"F2 stage pole count p={p} {label} stage={j}", cnt == pred, {"count": cnt, "pred": pred})
        stages.append({"stage": j, "affine_pole_count": cnt})
    f2.append({"p": p, "r": rr, "s": ss, "label": label, "stages": stages})

# F2b. The explicit family's 8 | #E (rational Z/2 x Z/4 on E').
for p, rr, ss, label in CHAIN_F2[:1]:
    Ac, Bc = -(rr + ss) % p, rr * ss % p
    nE = len(rational_points(p, Ac, Bc))
    record(f"F2b 8 | #E(F_{p}) for explicit family", nE % 8 == 0, {"order": nE})

# F3/F4. Odd one-anchor variant: first step and raw moments with symbolic odd weights.
def odd_raw_moments_symbolic(p):
    names = {}
    nu = {}
    for z in range(1, p):
        rep = min(z, p - z)
        if rep not in names:
            names[rep] = V(f"w{rep}")
        nu[z] = names[rep]
    svar = sum((nu[z] for z in range(1, p)), Poly(0))
    vvar = sum((nu[z] * nu[z] for z in range(1, p)), Poly(0))
    u3 = sum((nu[z] ** 3 for z in range(1, p)), Poly(0))

    def Gamma(cc):
        tot = Poly(0)
        for z in range(1, p):
            w = cc * pow(z, p - 2, p) % p
            if w != z:
                tot = tot + nu[z] * nu[w]
        return tot

    Edm, Edv, formula_v = Poly(0), Poly(0), Poly(0)
    for a0 in range(1, p):
        a2 = a0 * a0 % p
        # pushforward of nu under F(z)=z-a^2/z, residual (nonzero finite) part
        new = {}
        for z in range(1, p):
            b = (z - a2 * pow(z, p - 2, p)) % p
            if b != 0:
                new[b] = new.get(b, Poly(0)) + nu[z]
        vnew = sum((q * q for q in new.values()), Poly(0))
        zero_mass = nu[a0] + nu[p - a0]
        Edm = Edm + nu[a0] * zero_mass
        Edv = Edv + nu[a0] * (vnew - vvar)
        formula_v = formula_v + nu[a0] * Gamma((-a2) % p)
        identity(f"F4 p={p} a={a0}: v_new-v = Gamma(-a^2)-4nu(a)^2",
                 vnew - vvar, Gamma((-a2) % p) - 4 * nu[a0] ** 2)
    identity(f"F4 p={p}: E[1_legal dm] = 2v", Edm, 2 * vvar)
    identity(f"F4 p={p}: E[1_legal dv] = sum nu Gamma(-a^2) - 4u3", Edv, formula_v - 4 * u3)


for p in (7, 13):
    odd_raw_moments_symbolic(p)
    # F3: uniform affine start S=X: nu=1/p on F_p^*, first-step v_new exact
    for a0 in range(1, p):
        a2 = a0 * a0 % p
        new = {}
        for z in range(1, p):
            b = (z - a2 * pow(z, p - 2, p)) % p
            if b:
                new[b] = new.get(b, 0) + Fraction(1, p)
        vnew = sum(q * q for q in new.values())
        target = Fraction(2 * p - 6, p * p) if p % 4 == 3 else Fraction(2 * p - 8, p * p)
        record(f"F3 p={p} a={a0}: first-step residual collision mass", vnew == target, str(vnew))


# F5. Coalesced fold G_y on a GENERIC (non-square-carried) law: dm=nu(y), dv=Gamma(y^2)-nu(y)^2.
def coalesced_generic(p):
    nu = {z: V(f"g{z}") for z in range(1, p)}
    vvar = sum((nu[z] * nu[z] for z in range(1, p)), Poly(0))
    for y0 in range(1, p):
        cc = y0 * y0 % p
        new, zero = {}, Poly(0)
        for z in range(1, p):
            b = (z - 2 * y0 + cc * pow(z, p - 2, p)) % p
            if b == 0:
                zero = zero + nu[z]
            else:
                new[b] = new.get(b, Poly(0)) + nu[z]
        vnew = sum((q * q for q in new.values()), Poly(0))
        G = Poly(0)
        for z in range(1, p):
            w = cc * pow(z, p - 2, p) % p
            if w != z:
                G = G + nu[z] * nu[w]
        identity(f"F5 p={p} y={y0}: coalesced zero mass = nu(y)", zero, nu[y0])
        identity(f"F5 p={p} y={y0}: coalesced dv = Gamma(y^2)-nu(y)^2", vnew - vvar, G - nu[y0] ** 2)


coalesced_generic(7)


# F6. Fourier identity, exact in Q(zeta_n), n=p-1.
CYCLO = {6: [1, -1, 1], 12: [1, 0, -1, 0, 1]}  # Phi_6 = x^2-x+1, Phi_12 = x^4-x^2+1 (low->high)


def cyc_reduce(coeffs, n):
    phi = CYCLO[n]
    deg = len(phi) - 1
    c2 = list(coeffs)
    for i in range(len(c2) - 1, deg - 1, -1):
        q = c2[i]
        if q:
            for j in range(deg + 1):
                c2[i - deg + j] -= q * phi[j]
    return c2[:deg]


def cyc_check_phi(n):
    # Phi_n divides x^n - 1 and has degree phi(n)
    xn = [Fraction(-1)] + [Fraction(0)] * (n - 1) + [Fraction(1)]
    return all(z == 0 for z in cyc_reduce(xn, n))


def fourier_check(p, weights, label):
    n = p - 1
    assert cyc_check_phi(n)
    g = next(gg for gg in range(2, p) if all(pow(gg, n // q, p) != 1 for q in {2, 3} if n % q == 0))
    dlog = {pow(g, e, p): e for e in range(n)}

    def zeta_pow(e):  # element zeta^e as coefficient list length n
        v0 = [Fraction(0)] * n
        v0[e % n] = Fraction(1)
        return v0

    def mul(x1, x2):
        out = [Fraction(0)] * (2 * n)
        for i, ai in enumerate(x1):
            if ai:
                for j, bj in enumerate(x2):
                    if bj:
                        out[(i + j) % n] += ai * bj
        return out[:n]

    def add(x1, x2):
        return [ai + bi for ai, bi in zip(x1, x2)]

    def M(j):  # sum nu(x) eta_j(x), eta_j(g^e)=zeta^(j e)
        tot = [Fraction(0)] * n
        for xx in range(1, p):
            tot = add(tot, [weights[xx] * z for z in zeta_pow(j * dlog[xx])])
        return tot

    total = [Fraction(0)] * n
    for j in range(n):
        term = mul(mul(M(j), M(j)), zeta_pow(-j * dlog[p - 1]))  # conj(eta(-1)) = eta(-1)^{-1}
        term = mul(term, M((-2 * j) % n))
        total = add(total, term)
    lhs_red = cyc_reduce(total + [Fraction(0)] * n, n)
    Cconv = {cc: sum(weights[aa] * weights[cc * pow(aa, p - 2, p) % p] for aa in range(1, p)) for cc in range(1, p)}
    direct = sum(weights[yy] * Cconv[(-yy * yy) % p] for yy in range(1, p))
    rhs = [Fraction(direct * n)] + [Fraction(0)] * (len(lhs_red) - 1)
    record(f"F6 Fourier identity exact p={p} {label}", lhs_red == rhs, {"direct": str(direct)})


W7 = {1: Fraction(1, 10), 2: Fraction(3, 20), 3: Fraction(1, 20), 4: Fraction(1, 20), 5: Fraction(3, 20), 6: Fraction(1, 10)}
fourier_check(7, W7, "odd weights")
W7g = {1: Fraction(1, 7), 2: Fraction(2, 21), 3: Fraction(1, 21), 4: Fraction(5, 42), 5: Fraction(1, 6), 6: Fraction(1, 14)}
fourier_check(7, W7g, "non-odd weights")
W13 = {z: Fraction(1 + min(z, 13 - z), 60) for z in range(1, 13)}
fourier_check(13, W13, "odd weights")


# F7. Odd variant, p = 3 mod 4: torus schedule c->4c versus elliptic c->-4c, supply laws.
f7 = []
for p in (7, 11, 19, 23):
    for a0 in (1, 3):
        c0 = (-a0 * a0) % p  # F(z) = z + c/z, c = -a^2
        tor = [(0, (4**j) * c0 % p) for j in range(6)]
        ell = [(0, ((-4) ** j) * c0 % p) for j in range(6)]
        ft = [fold_chain_first_pole(p, x0, tor)[0] for x0 in range(p)]
        fe = [fold_chain_first_pole(p, x0, ell)[0] for x0 in range(p)]
        for j in range(1, 7):
            cnt = sum(1 for t in ft if t is not None and t <= j)
            record(f"F7 torus p={p} a={a0} stage={j}: (gcd(p+1,2^j)-1)", cnt == gcd(p + 1, 2**j) - 1, cnt)
        for k in range(1, 4):
            cnt = sum(1 for t in fe if t is not None and t <= 2 * k)
            record(f"F7 elliptic p={p} a={a0} k={k}: (gcd(p+1,2^(k+1))-1)", cnt == gcd(p + 1, 2 ** (k + 1)) - 1, cnt)
        # group orders: curve Y^2=X^3-a^2X and twist both p+1
        nE = len(rational_points(p, 0, (-a0 * a0) % p))
        d = nonsquare(p)
        At, Bt = twist_coeffs(p, 0, (-a0 * a0) % p, d)
        nT = len(rational_points(p, At, Bt))
        record(f"F7 p={p} a={a0}: #E = #E^d = p+1", nE == p + 1 == nT, [nE, nT])
    f7.append(p)


# F8. Composite stopped versus final-only success, one fixed N=11*13, explicit family u=2,v=3.
def local_first(p, rr, ss, depth):
    sched = coherent_schedule(rr, ss, depth, p)
    return [fold_chain_first_pole(p, x0, sched)[0] for x0 in range(p)]


pN, qN, depthN = 11, 13, 6
NN = pN * qN
rN, sN = 4, 9
assert all(gcd(t, NN) == 1 for t in (2, 2, 3, 2 - 3, 2 + 3))
schedN = coherent_schedule(rN, sN, depthN, NN)
stopped_succ = final_succ = 0
for x0 in range(NN):
    Uc, Vc = x0, 1
    hit = None
    for j, (S, P) in enumerate(schedN, start=1):
        Uc, Vc = (Uc * Uc - S * Uc * Vc + P * Vc * Vc) % NN, (Uc * Vc) % NN
        g = gcd(Vc, NN)
        if g != 1 and hit is None:
            hit = g
    # stopped: first non-unit gcd over stages
    if hit is not None and 1 < hit < NN:
        stopped_succ += 1
    gfin = gcd(Vc, NN)
    if 1 < gfin < NN:
        final_succ += 1
fp_, fq_ = local_first(pN, rN, sN, depthN), local_first(qN, rN, sN, depthN)
pred_stop = sum(1 for a1 in fp_ for b1 in fq_ if (a1 is not None or b1 is not None) and a1 != b1)
Hp = sum(1 for t in fp_ if t is not None)
Hq = sum(1 for t in fq_ if t is not None)
pred_final = Hp * (qN - Hq) + Hq * (pN - Hp)
record("F8 stopped per-stage gcd success = P(tau_p != tau_q, min<=D) by CRT", stopped_succ == pred_stop,
       {"count": stopped_succ, "pred": pred_stop, "N": NN})
record("F8 final denominator-only success = h_p(1-h_q)+h_q(1-h_p)", final_succ == pred_final,
       {"count": final_succ, "pred": pred_final})

out = {
    "scope": "exact symbolic identities plus fixed preregistered tiny-field certificates; no search/sweep/run",
    "total": len(checks),
    "passed": sum(c["passed"] for c in checks),
    "f1_curves": f1,
    "f2_chains": f2,
    "f7_primes": f7,
    "f8": {"N": NN, "depth": depthN, "stopped_success_inputs": stopped_succ, "final_only_success_inputs": final_succ},
    "checks": checks,
}
Path("research/findings/W009-escape-review-check.json").write_text(json.dumps(out, indent=1) + "\n")
print(out["passed"], "/", out["total"], "checks passed;", "F8:", out["f8"])
