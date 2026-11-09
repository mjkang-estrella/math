"""Exact W009 two-anchor reciprocal review evidence; not a factoring candidate.

Symbolic stdlib polynomial identities, plus fixed small-field instance
certificates (symbolic weights over F_5 and F_7; exact flat laws on the
subgroups of F_13). No parameter search, prime sweep, depth sweep or run.
Run from the factoring-research root; writes only the owned evidence JSON.
"""

from fractions import Fraction
from itertools import product
from pathlib import Path
import json


class Poly:
    """Sparse multivariate polynomial over Q, keys are sorted (var, exp) tuples."""

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


def identity(name, left, right):
    ok = (Poly.c(left) - Poly.c(right)).zero()
    checks.append({"name": name, "passed": ok})
    assert ok, name


def det(m):
    if len(m) == 1:
        return m[0][0]
    total = Poly(0)
    for j in range(len(m)):
        minor = [row[:j] + row[j + 1:] for row in m[1:]]
        term = Poly.c(m[0][j]) * det(minor)
        total = total + term if j % 2 == 0 else total - term
    return total


z, u, y, w, U, Vv, r, s0 = (V(n) for n in ("z", "u", "y", "w", "U", "V", "r", "s0"))
c = y * w

# (1) projective update equals F on the affine chart: F*z = (z-y)(z-w).
identity("F affine form: (z-y)(z-w) = z^2-(y+w)z+c", (z - y) * (z - w), z * z - (y + w) * z + c)
# Resultant of f=(U-yV)(U-wV)=U^2-(y+w)UV+cV^2 and g=UV (Sylvester, deg 2 each).
f2, f1, f0 = Poly(1), -(y + w), c
syl = [[f2, f1, f0, 0], [0, f2, f1, f0], [0, 1, 0, 0], [0, 0, 1, 0]]
identity("Res((U-yV)(U-wV), UV) = y*w  (no basepoint iff c unit)", det(syl), c)
# Images of the marked points, projectively: [U:V] -> [f(U,V) : U V].
fUV = lambda a, b: ((a - y * b) * (a - w * b), a * b)
for label, pt, expect in (("0", (0, 1), (c, 0)), ("inf", (1, 0), (1, 0)),
                          ("y", (y, 1), (0, y)), ("w", (w, 1), (0, w))):
    got = fUV(Poly.c(pt[0]), Poly.c(pt[1]))
    identity(f"F({label}) numerator", got[0], expect[0])
    identity(f"F({label}) denominator", got[1], expect[1])

# (2) F(z)-F(u) times z*u.
Fz_num = (z - y) * (z - w)
Fu_num = (u - y) * (u - w)
identity("(2) u*Fz_num - z*Fu_num = (z-u)(zu-c)", u * Fz_num - z * Fu_num, (z - u) * (z * u - c))
# iota_c fiber automorphism: F(c/z)=(c-yz)(c-wz)/(cz), equal to F(z) by:
identity("(c-yz)(c-wz) = c*(z-y)(z-w)  [uses c=yw]", (c - y * z) * (c - w * z), c * (z - y) * (z - w))

# Torus/Newton conjugacy: with r^2=c, (z+c/z-2r)/(z+c/z+2r) = ((z-r)/(z+r))^2.
cr = r * r
identity("conjugacy: (z^2+c-2rz)(z+r)^2 = (z-r)^2 (z^2+c+2rz), c=r^2",
         (z * z + cr - 2 * r * z) * (z + r) ** 2, (z - r) ** 2 * (z * z + cr + 2 * r * z))
identity("iota_c is x -> -x: (c/z - r)(z + r) = -(z - r)(c/z + r) cleared by z",
         (cr - r * z) * (z + r), -(z - r) * (cr + r * z))
# Frame alignment: output frame points are -s0 +- 2r; next input frame is +- r'.
# Equality as sets forces s0=0 and r'^2 = 4 r^2 (sum and product of the two pairs).
identity("output-frame pair product (-s0+2r)(-s0-2r) = s0^2 - 4c", (-s0 + 2 * r) * (-s0 - 2 * r), s0 * s0 - 4 * cr)

# (4) closed form on symbolic weights over F_p, p=5 and 7 (instance certificates).
summation = []
for p in (5, 7):
    units = list(range(1, p))
    nu = {a: V(f"n{a}") for a in units}
    s = sum((nu[a] for a in units), Poly(0))
    v = sum((nu[a] ** 2 for a in units), Poly(0))
    u3 = sum((nu[a] ** 3 for a in units), Poly(0))
    q4 = sum((nu[a] ** 4 for a in units), Poly(0))
    gamma = {cc: sum((nu[a] * nu[b] for a in units for b in units if a != b and a * b % p == cc), Poly(0))
             for cc in units}
    ell2 = sum((nu[a] * nu[b] for a in units for b in units if a != b), Poly(0))
    identity(f"F_{p}: ell2 = s^2 - v", ell2, s * s - v)
    identity(f"F_{p}: sum_c Gamma(c) = ell2", sum(gamma.values(), Poly(0)), ell2)
    # pointwise (3) summed over legal ordered pairs, with v_new computed from orbits.
    lhs_drift = Poly(0)
    lhs_abs = Poly(0)
    for yy, ww in product(units, units):
        if yy == ww:
            continue
        cc = yy * ww % p
        orbits = {frozenset((a, cc * pow(a, -1, p) % p)) for a in units}
        vnew = Poly(0)
        for orb in orbits:
            if orb == frozenset((yy, ww)):
                continue
            vnew = vnew + sum((nu[a] for a in orb), Poly(0)) ** 2
        identity(f"F_{p}: pointwise (3) at y={yy},w={ww}",
                 vnew - v, gamma[cc] - (nu[yy] + nu[ww]) ** 2)
        lhs_drift = lhs_drift + nu[yy] * nu[ww] * (vnew - v)
        lhs_abs = lhs_abs + nu[yy] * nu[ww] * (nu[yy] + nu[ww])
    energy = sum((g * g for g in gamma.values()), Poly(0))
    identity(f"F_{p}: (4) drift numerator", lhs_drift, energy - 2 * s * u3 - 2 * v * v + 4 * q4)
    identity(f"F_{p}: (4) absorption numerator", lhs_abs, 2 * (s * v - u3))
    summation.append(p)

# Subgroup drift: symbolic rational simplification in m and s.
m, S = V("m"), V("S")
# odd: numerator s^4[(m-1)^2 - 4m + 4]/m^3 = s^4 (m-1)(m-5)/m^3; divide by ell2=s^2(m-1)/m.
identity("odd subgroup numerator", (m - 1) ** 2 - 4 * m + 4, (m - 1) * (m - 5))
# even: (m/2)[(m-2)^2+m^2] = m(m^2-2m+2); minus 4m-4 after scaling by m^3/s^4.
identity("even subgroup energy", Fraction(1, 2) * ((m - 2) ** 2 + m * m), m * m - 2 * m + 2)
identity("even subgroup numerator", m * m - 2 * m + 2 - 4 * m + 4, m * m - 6 * m + 6)

# Exact flat-subgroup instances in F_13 (every subgroup), averaged over the actual sampler.
P13 = 13
subgroup_rows = []
for d in (1, 2, 3, 4, 6, 12):
    G = sorted({pow(2, (12 // d) * k, P13) for k in range(d)})  # 2 generates F_13^*
    mm = len(G)
    if mm < 2:
        subgroup_rows.append({"m": mm, "ell2": 0, "note": "ell2=0: legal event empty, conditional law undefined"})
        continue
    sm = Fraction(1)
    nuG = {a: sm / mm for a in G}
    num = Fraction(0)
    ell = Fraction(0)
    for yy, ww in product(G, G):
        if yy == ww:
            continue
        cc = yy * ww % P13
        orbits = {frozenset((a, cc * pow(a, -1, P13) % P13)) for a in G}
        assert all(cc * pow(a, -1, P13) % P13 in nuG for a in G)  # iota_c preserves G
        vnew = sum(sum(nuG[a] for a in o) ** 2 for o in orbits if o != frozenset((yy, ww)))
        wgt = nuG[yy] * nuG[ww]
        ell += wgt
        num += wgt * (vnew - sum(x * x for x in nuG.values()))
    drift = num / ell
    formula = (Fraction(mm - 5, mm * mm) if mm % 2 else Fraction(mm * mm - 6 * mm + 6, mm * mm * (mm - 1))) * sm ** 2
    assert drift == formula, (mm, drift, formula)
    subgroup_rows.append({"m": mm, "drift": str(drift), "formula": str(formula),
                          "relative_to_v": str(drift / (sm ** 2 / mm))})

# Uniform affine start on F_13 IS the m=12 flat subgroup case; trace counts for one
# square and one nonsquare product c (fixed pairs, not a search).
trace_rows = []
for yy, ww in ((1, 4), (1, 2)):  # c=4 square, c=2 nonsquare mod 13
    cc = yy * ww % P13
    chi = lambda x: 0 if x % P13 == 0 else (1 if pow(x, 6, P13) == 1 else -1)
    counts = {b: 0 for b in range(P13)}
    n_inf = 0
    for x in range(P13):
        if x == 0:
            n_inf += 1
        else:
            counts[(x + cc * pow(x, -1, P13) - yy - ww) % P13] += 1
    assert all(counts[b] == 1 + chi((b + yy + ww) ** 2 - 4 * cc) for b in range(P13))
    assert n_inf == 1 and counts[0] == 2 and sum(counts.values()) + n_inf == P13
    zc = sum(1 for x in range(P13) if (x * x - 4 * cc) % P13 == 0)
    vnew = Fraction(sum(n * n for b, n in counts.items() if b != 0), P13 ** 2)
    assert vnew == Fraction(2 * P13 - 6 - zc, P13 ** 2)
    trace_rows.append({"y": yy, "w": ww, "c": cc, "chi_c": chi(cc), "v_new": str(vnew),
                       "delta_v": str(vnew - Fraction(P13 - 1, P13 ** 2))})

# (5) channel decomposition, symbolic in local color probabilities (r = 1 - z - h).
zp, hp, zq, hq = V("zp"), V("hp"), V("zq"), V("hq")
rp, rq = 1 - zp - hp, 1 - zq - hq
s_factor = 1 - rp * rq - zp * zq - hp * hq
s_V = hp * (1 - hq) + hq * (1 - hp)
ap, aq = zp + hp, zq + hq
s_UV = ap * (1 - aq) + aq * (1 - ap)
identity("(5) s_factor - s_V = z_p r_q + z_q r_p", s_factor - s_V, zp * rq + zq * rp)
identity("(5) s_factor - s_UV = z_p h_q + h_p z_q", s_factor - s_UV, zp * hq + hp * zq)
identity("(5) mixed-state sum", s_factor, zp * (rq + hq) + hp * (rq + zq) + rp * (zq + hq))

# Two-color masking certificate (symbolic in the state, exact): a stage-K zero at p
# becomes infinity at stage K+1, so (zero@p, inf@q) -> (inf, inf): proper gcd lost.
masking = {"stage_K": "U=0 mod p, V=0 mod q -> gcd(U,N)=p proper",
           "stage_K+1": "F(0)=F(inf)=inf at both primes -> V=0 mod N, U unit: full gcd only"}

result = {"passed": True, "symbolic_identities": len(checks), "checks": checks,
          "summation_fields": summation, "F13_subgroups": subgroup_rows,
          "F13_uniform_trace": trace_rows, "two_color_masking": masking}
Path("research/findings/W009-reciprocal-review-check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ("passed", "symbolic_identities", "F13_subgroups", "F13_uniform_trace")}, indent=1))
