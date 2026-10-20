#!/usr/bin/env python3
# Independent exact certificate for (S)_4, T088P133 correctness review round2.
# Author of this file: review sub-agent (round2). MIT License.
#
# Method (deliberately different from the author's certificate.py, which builds
# alternating Vandermonde sums and divides factor by factor):
#   1. Build M := 5*Np~*V*Den - D*Np~^2 as an EXPLICIT polynomial (no division),
#      where Np~, NP~ are the alternating-sums from Lemma 7 (proved analytically
#      in review.md: p = Np~/(V*Den), E W^+ = NP~/(V*Den) as rational identities).
#   2. Recover the candidate quotient T by EXACT MULTIVARIATE INTERPOLATION:
#      evaluate r(x,y) := Den^2*(5P - D*p^2) at every point of a tensor grid of
#      positive integers (all entries distinct there), with p, P computed
#      DIRECTLY from Lemma 7's partial-fraction formula in exact rational
#      arithmetic. Grid size per variable exceeds deg(M) in that variable, so a
#      polynomial T with T*V^2 = M (if one exists) is the unique interpolant.
#   3. Verify the candidate EXACTLY by symbolic multiplication: T*V^2 - M == 0
#      as a polynomial (empty coefficient dict). This proves 5P - Dp^2 = T/Den^2
#      on the dense set, with T the interpolated polynomial.
#   4. Inspect T's coefficients: all >= 0; existence of a strictness monomial in
#      the always-positive variables x_k, y_l only.
# No randomness anywhere. Pure Python, Fractions only. One process.
import sys
from fractions import Fraction as Fr

sys.dont_write_bytecode = True


# ---------- exact multivariate polynomials: {exponent tuple: Fraction} ----------
class Poly:
    __slots__ = ("t", "nv")

    def __init__(self, t, nv):
        self.t = {k: v for k, v in t.items() if v != 0}
        self.nv = nv

    @staticmethod
    def var(i, nv):
        e = [0] * nv
        e[i] = 1
        return Poly({tuple(e): Fr(1)}, nv)

    @staticmethod
    def const(c, nv):
        return Poly({(0,) * nv: Fr(c)}, nv)

    def __add__(self, o):
        o = o if isinstance(o, Poly) else Poly.const(o, self.nv)
        r = dict(self.t)
        for k, v in o.t.items():
            r[k] = r.get(k, Fr(0)) + v
        return Poly(r, self.nv)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()}, self.nv)

    def __sub__(self, o):
        return self + (-(o if isinstance(o, Poly) else Poly.const(o, self.nv)))

    def __mul__(self, o):
        o = o if isinstance(o, Poly) else Poly.const(o, self.nv)
        r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                r[k] = r.get(k, Fr(0)) + v1 * v2
        return Poly(r, self.nv)

    __rmul__ = __mul__

    def __pow__(self, e):
        r = Poly.const(1, self.nv)
        for _ in range(e):
            r = r * self
        return r

    def scale(self, c):
        return Poly({k: v * c for k, v in self.t.items()}, self.nv)

    def __call__(self, x):
        s = Fr(0)
        for k, v in self.t.items():
            m = v
            for xi, a in zip(x, k):
                if a:
                    m *= xi ** a
            s += m
        return s

    def deg(self, i):
        return max((k[i] for k in self.t), default=0)

    def is_zero(self):
        return not self.t


# ---------- symbolic constructions (from the Lemma-7 partial fractions) ----------
def build_M(k, l, z):
    """Explicit M = 5*NP~*V*Den - D*Np~^2 as a polynomial in x_1..x_k, y_1..y_l."""
    n = k + l + z
    assert n == 4 or n == 5
    nv = k + l
    X = [Poly.var(i, nv) for i in range(k)]
    Y = [Poly.var(k + j, nv) for j in range(l)]
    u = []
    for i in range(k):
        s = Poly.const(0, nv)
        for j in range(i, k):
            s = s + X[j]
        u.append(s)  # u_i = x_i + ... + x_k
    v = []
    for j in range(l):
        s = Poly.const(0, nv)
        for jj in range(j, l):
            s = s + Y[jj]
        v.append(s)  # v_j = y_j + ... + y_l

    def vandermonde(lst):
        r = Poly.const(1, nv)
        for a in range(len(lst)):
            for b in range(a + 1, len(lst)):
                r = r * (lst[a] - lst[b])
        return r

    V = vandermonde(u)
    Den = Poly.const(1, nv)
    for i in range(k):
        for j in range(l):
            Den = Den * (u[i] + v[j])

    # Alternating sums:  Np~ = sum_i (-1)^{i-1} u_i^{k-1+l} V(u \ u_i) prod_{i'!=i,j} (u_{i'}+v_j)
    #                    NP~ = same with exponent k+l   (1-based sign convention)
    def alt_sum(extra):
        tot = Poly.const(0, nv)
        for i in range(k):
            term = (u[i] ** (k - 1 + l + extra)) * vandermonde([u[a] for a in range(k) if a != i])
            for a in range(k):
                if a != i:
                    for j in range(l):
                        term = term * (u[a] + v[j])
            tot = tot + term.scale(Fr(1) if i % 2 == 0 else Fr(-1))
        return tot

    Np_tilde = alt_sum(0)
    NP_tilde = alt_sum(1)

    # D(b): sorted entries s_1<=..<=s_4 are  -v_1 .. -v_l, 0^z, u_k .. u_1 ; D = sum (2i-m-1) s_i
    srt = [(-v[j]) for j in range(l)] + [Poly.const(0, nv)] * z + [u[i] for i in reversed(range(k))]
    m = len(srt)
    D = Poly.const(0, nv)
    for i, s in enumerate(srt):
        D = D + s.scale(Fr(2 * (i + 1) - m - 1))

    M = (Poly.const(n + 1, nv) * NP_tilde * V * Den) - (D * Np_tilde * Np_tilde)
    return M, V, Den, u, v


# ---------- direct Lemma-7 evaluation at a rational point ----------
def direct_pP(u_vals, v_vals):
    """p = P(W>0), P = E W^+ for W = sum u_i E^+_i - sum v_j E^-_j, exact, distinct entries."""
    cs = list(u_vals) + [-t for t in v_vals]
    p = Fr(0)
    P = Fr(0)
    for j, cj in enumerate(cs):
        if cj > 0:
            A = Fr(1)
            for i, ci in enumerate(cs):
                if i != j:
                    A *= Fr(cj) / (cj - ci)
            p += A
            P += A * cj
    return p, P


def direct_D(u_vals, v_vals, z):
    s = sorted(list(u_vals) + [-t for t in v_vals] + [Fr(0)] * z)
    m = len(s)
    return sum((2 * (i + 1) - m - 1) * s[i] for i in range(m))


# ---------- multivariate exact interpolation (tensor Newton) ----------
def interpolate(nv, deltas, value_fn):
    """Interpolate polynomial with per-variable degree <= deltas[i] from values on
    the integer grid x_i in {1..deltas[i]+1}. Newton form per variable, Poly-valued."""
    nodes = [[Fr(t) for t in range(1, deltas[i] + 2)] for i in range(nv)]
    # gather grid values
    grid = {}

    def rec(i, prefix):
        if i == nv:
            grid[tuple(prefix)] = value_fn(prefix)
            return
        for val in nodes[i]:
            rec(i + 1, prefix + [val])

    rec(0, [])

    # iterative 1D Newton interpolation along each variable, coefficients are Polys.
    # Invariant: before processing variable `var`, data maps a tuple of nodes for
    # variables var..nv-1 (in order) to a Poly in variables 0..var-1.
    data = {pt: Poly.const(grid[pt], 0) for pt in grid}  # start: 0-variable polys
    for var in range(nv):
        nd = nodes[var]
        groups = {}
        for pt, poly in data.items():
            groups.setdefault(pt[1:], []).append(pt)
        newdata = {}
        for key, pts in groups.items():
            pts.sort(key=lambda pt: pt[0])
            ys = [data[pt] for pt in pts]
            # Newton divided differences with Poly coefficients
            coefs = ys[:]
            for j in range(1, len(nd)):
                for i in range(len(nd) - 1, j - 1, -1):
                    coefs[i] = (coefs[i] - coefs[i - 1]).scale(Fr(1) / (nd[i] - nd[i - j]))
            # expand Newton basis to a Poly in variables 0..var
            result = Poly.const(0, nv)
            basis = Poly.const(1, nv)
            for j in range(len(nd)):
                lifted = Poly({}, nv)
                for kk, vv in coefs[j].t.items():
                    # coefs[j] is a Poly in variables 0..var-1 (exponent tuple length var)
                    e = list(kk) + [0] * (nv - len(kk))
                    lifted.t[tuple(e)] = vv
                result = result + lifted * basis
                basis = basis * (Poly.var(var, nv) - Poly.const(nd[j], nv))
            newdata[key] = result
        data = newdata
    assert len(data) == 1
    return next(iter(data.values()))


def check_pattern(k, l, z):
    n = k + l + z
    nv = k + l
    M, V, Den, u, v = build_M(k, l, z)
    if nv == 0:
        # b has a single positive entry only possible for k>=1,nv=0 never (k>=1 => nv>=1)
        raise AssertionError
    deltas = [M.deg(i) for i in range(nv)]

    def value_fn(pt):
        x = pt[:k]
        y = pt[k:]
        u_vals = [sum(x[i:]) for i in range(k)]
        v_vals = [sum(y[j:]) for j in range(l)]
        p, P = direct_pP(u_vals, v_vals)
        D = direct_D(u_vals, v_vals, z)
        den = Fr(1)
        for uu in u_vals:
            for vv in v_vals:
                den *= (uu + vv)
        return den * den * (Fr(n + 1) * P - D * p * p)

    T = interpolate(nv, deltas, value_fn)
    # exact verification: T * V^2 - M == 0 as a polynomial
    Q = T * V * V - M
    verified = Q.is_zero()
    # coefficient analysis
    coeffs = list(T.t.values())
    nonneg = all(c > 0 for c in coeffs)  # zero coefficients are not stored
    min_coeff = min(coeffs) if coeffs else Fr(0)
    pos_idx = {k - 1} | ({k + l - 1} if l > 0 else set())
    strict_mono = any(all(e == 0 for i, e in enumerate(key) if i not in pos_idx) for key in T.t)
    return dict(pattern=(k, l, z), terms=len(T.t), min_coeff=min_coeff, nonneg=nonneg,
                strict_monomial=strict_mono, verified_TVsqr_eq_M=verified, T=T)


def main():
    n = 4
    ok = True
    print("Independent (S)_4 certificate via exact interpolation + symbolic T*V^2 == M")
    results = {}
    for k in range(1, n + 1):
        for l in range(0, n - k + 1):
            z = n - k - l
            r = check_pattern(k, l, z)
            results[(k, l, z)] = r
            good = r["verified_TVsqr_eq_M"] and r["nonneg"] and (r["strict_monomial"] or l == 0)
            ok &= good
            print("  pattern", (k, l, z), "terms", r["terms"], "min_coeff", r["min_coeff"],
                  "nonneg", r["nonneg"], "strict_mono", r["strict_monomial"],
                  "T*V^2==M", r["verified_TVsqr_eq_M"], "OK" if good else "FAIL")
    # negative control: n=5 pattern (4,1,0) must NOT be nonnegative (consistency only)
    r5 = check_pattern(4, 1, 0)
    neg_ok = r5["verified_TVsqr_eq_M"] and not r5["nonneg"]
    ok &= neg_ok
    print("negative control n=5 (4,1,0): verified", r5["verified_TVsqr_eq_M"],
          "nonneg", r5["nonneg"], "min_coeff", r5["min_coeff"], "OK" if neg_ok else "FAIL")
    print("INDEPENDENT CERTIFICATE", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
