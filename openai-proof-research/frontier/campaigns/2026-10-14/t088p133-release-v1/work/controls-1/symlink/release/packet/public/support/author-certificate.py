#!/usr/bin/env python3
# MIT License. Author: Myeongjin Kang. Exact certificate for Proposition C (inequality (S)_4) of proof.md.
# Pure Python (fractions only). Deterministic. Runtime: a few seconds; memory: small.
#
# For a sign pattern (k, l, z) of b in R^n (k positive, l negative, z zero entries) we use ordered variables
#   x_1..x_k >= 0, y_1..y_l >= 0, u_i = x_i + ... + x_k, v_j = y_j + ... + y_l,
# so the positive entries are u_1 >= ... >= u_k > 0 and the negative entries are -v_1 <= ... <= -v_l < 0.
# With Den = prod_{i,j} (u_i + v_j) the proof shows P(W>0) = Np/Den and E W^+ = NP/Den, where
#   Np = sum_i (-1)^(i-1) u_i^(k-1+l) V(u without u_i) prod_{i' != i, j} (u_i' + v_j) / V(u),
#   NP = same with exponent k+l,
# V = Vandermonde prod_{a<b}(u_a - u_b). The certificate polynomial is T = (n+1) NP Den - D(b) Np^2.
import sys
import random
from fractions import Fraction as Fr

sys.dont_write_bytecode = True


class Poly:
    __slots__ = ("t", "nv")

    def __init__(self, t, nv):
        self.t = {k: v for k, v in t.items() if v != 0}
        self.nv = nv

    @staticmethod
    def var(i, nv):
        e = [0] * nv
        e[i] = 1
        return Poly({tuple(e): 1}, nv)

    @staticmethod
    def const(c, nv):
        return Poly({(0,) * nv: c}, nv)

    def _c(self, o):
        return o if isinstance(o, Poly) else Poly.const(o, self.nv)

    def __add__(self, o):
        o = self._c(o)
        r = dict(self.t)
        for k, v in o.t.items():
            r[k] = r.get(k, 0) + v
        return Poly(r, self.nv)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.t.items()}, self.nv)

    def __sub__(self, o):
        return self + (-self._c(o))

    def __mul__(self, o):
        o = self._c(o)
        r = {}
        for k1, v1 in self.t.items():
            for k2, v2 in o.t.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                r[k] = r.get(k, 0) + v1 * v2
        return Poly(r, self.nv)

    __rmul__ = __mul__

    def __pow__(self, e):
        r = Poly.const(1, self.nv)
        for _ in range(e):
            r = r * self
        return r

    def divexact(self, d):
        q = Poly({}, self.nv)
        r = Poly(dict(self.t), self.nv)
        lt_d = max(d.t)
        cd = d.t[lt_d]
        while r.t:
            lt = max(r.t)
            if any(a < b for a, b in zip(lt, lt_d)):
                raise ValueError("not divisible")
            m = Poly({tuple(a - b for a, b in zip(lt, lt_d)): Fr(r.t[lt]) / cd}, self.nv)
            q = q + m
            r = r - m * d
        return q

    def __call__(self, *x):
        s = 0
        for k, v in self.t.items():
            m = v
            for xi, a in zip(x, k):
                m *= xi ** a
            s += m
        return s


def build(k, l, z):
    n = k + l + z
    nv = k + l
    X = [Poly.var(i, nv) for i in range(k)]
    Y = [Poly.var(k + j, nv) for j in range(l)]
    zero = Poly.const(0, nv)
    u = [sum(X[i:], zero) for i in range(k)]
    v = [sum(Y[j:], zero) for j in range(l)]

    def vand(lst):
        r = Poly.const(1, nv)
        for a in range(len(lst)):
            for b in range(a + 1, len(lst)):
                r = r * (lst[a] - lst[b])
        return r

    def num(extra):
        tot = Poly.const(0, nv)
        for i in range(k):
            term = (u[i] ** (k - 1 + l + extra)) * vand([u[a] for a in range(k) if a != i])
            for a in range(k):
                if a != i:
                    for j in range(l):
                        term = term * (u[a] + v[j])
            tot = tot + (term if i % 2 == 0 else -term)
        for a in range(k):
            for b in range(a + 1, k):
                tot = tot.divexact(u[a] - u[b])
        return tot

    Np, NP = num(0), num(1)
    Den = Poly.const(1, nv)
    for i in range(k):
        for j in range(l):
            Den = Den * (u[i] + v[j])
    srt = [-v[j] for j in range(l)] + [zero] * z + [u[i] for i in reversed(range(k))]
    m = len(srt)
    D = zero
    for i, s in enumerate(srt):
        D = D + (2 * i - m + 1) * s
    T = (n + 1) * NP * Den - D * Np * Np
    return dict(Np=Np, NP=NP, Den=Den, D=D, T=T, nv=nv)


def partial_fraction_pP(b):
    """Direct partial-fraction formulas (distinct nonzero entries); zero entries ignored."""
    w = [x for x in b if x != 0]
    p = Fr(0)
    P = Fr(0)
    for j, c in enumerate(w):
        if c > 0:
            A = Fr(1)
            for i, d in enumerate(w):
                if i != j:
                    A *= Fr(c) / (c - d)
            p += A
            P += A * c
    return p, P


def Dfun(b):
    s = sorted(b)
    m = len(s)
    return sum((2 * i - m + 1) * s[i] for i in range(m))


def check_pattern(k, l, z, rng):
    R = build(k, l, z)
    T = R["T"]
    nv = R["nv"]
    nonneg = all(v >= 0 for v in T.t.values())
    # strictness: a monomial in the always-positive variables x_k, y_l only (indices k-1 and k+l-1)
    pos_idx = {k - 1} | ({k + l - 1} if l > 0 else set())
    strict_mono = any(v > 0 and all(e == 0 for i, e in enumerate(key) if i not in pos_idx) for key, v in T.t.items())
    # exact identity check against direct partial fractions at random rational distinct points
    ident = True
    for _ in range(5):
        xs = [Fr(rng.randint(1, 97), rng.randint(1, 13)) for _ in range(nv)]
        u = [sum(xs[i:k]) for i in range(k)]
        v = [sum(xs[k + j:]) for j in range(l)]
        b = u + [-t for t in v] + [Fr(0)] * z
        if len(set(x for x in b if x != 0)) < k + l:
            continue
        p, P = partial_fraction_pP(b)
        den = R["Den"](*xs)
        if R["Np"](*xs) != p * den or R["NP"](*xs) != P * den or R["D"](*xs) != Dfun(b):
            ident = False
    return dict(pattern=(k, l, z), terms=len(T.t), nonneg=nonneg, strict_monomial=strict_mono,
                min_coeff=min(T.t.values()) if T.t else 0, identity=ident)


def mc_check(rng, trials=200000):
    """Float Monte Carlo sanity check of the partial-fraction p and E W^+ (not part of the proof)."""
    b = [0.9, 0.35, -0.6, -0.15]
    p, P = partial_fraction_pP([Fr(x).limit_denominator(1000) for x in b])
    cnt = 0
    s = 0.0
    for _ in range(trials):
        w = sum(c * rng.expovariate(1.0) for c in b)
        if w > 0:
            cnt += 1
            s += w
    return float(p), cnt / trials, float(P), s / trials


def main():
    rng = random.Random(20261020)
    ok = True
    n = 4
    print("Proposition C certificate, n = 4: all sign patterns (k,l,z), k >= 1")
    for k in range(1, n + 1):
        for l in range(0, n - k + 1):
            z = n - k - l
            r = check_pattern(k, l, z, rng)
            need_strict = l >= 1
            good = r["nonneg"] and r["identity"] and (r["strict_monomial"] or not need_strict)
            ok &= good
            print(" ", r, "OK" if good else "FAIL")
    # negative control: the same checker must reject n = 5, pattern (4,1,0)
    r5 = check_pattern(4, 1, 0, rng)
    neg_ok = not r5["nonneg"]
    ok &= neg_ok
    print("negative control n=5 pattern (4,1,0): nonneg =", r5["nonneg"], "min_coeff =", r5["min_coeff"],
          "(expected False)", "OK" if neg_ok else "FAIL")
    p, pmc, P, Pmc = mc_check(rng)
    mc_ok = abs(p - pmc) < 0.01 and abs(P - Pmc) < 0.01
    ok &= mc_ok
    print("Monte Carlo sanity (float, not a proof): p=%.5f mc=%.5f  E W+=%.5f mc=%.5f %s" % (p, pmc, P, Pmc, "OK" if mc_ok else "FAIL"))
    print("CERTIFICATE", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
