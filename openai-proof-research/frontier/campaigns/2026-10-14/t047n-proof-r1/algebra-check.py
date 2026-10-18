#!/usr/bin/env python3
"""Independent exact identity checks for the T047N proof review. MIT.

Pure-Python Laurent polynomials over Q. These are finite checks of
displayed identities for n=2..NMAX; they certify no theorem.
"""
import json
import sys
from fractions import Fraction

VARS = ['p', 's', 'u', 'F', 'J', 'w', 'L', 'M', 'x', 'y', 'z', 'a', 'b', 'c', 'd', 'Z', 't']
IDX = {v: i for i, v in enumerate(VARS)}
NV = len(VARS)
NMAX = 7


class Poly:
    __slots__ = ('d',)

    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v != 0}

    @staticmethod
    def const(c):
        return Poly({(0,) * NV: Fraction(c)})

    @staticmethod
    def var(name, e=1):
        t = [0] * NV
        t[IDX[name]] = e
        return Poly({tuple(t): Fraction(1)})

    def _lift(self, o):
        return o if isinstance(o, Poly) else Poly.const(o)

    def __add__(self, o):
        o = self._lift(o)
        r = dict(self.d)
        for k, v in o.d.items():
            r[k] = r.get(k, 0) + v
        return Poly(r)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-self._lift(o))

    def __rsub__(self, o):
        return self._lift(o) - self

    def __mul__(self, o):
        o = self._lift(o)
        r = {}
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                r[k] = r.get(k, 0) + v1 * v2
        return Poly(r)

    __rmul__ = __mul__

    def __pow__(self, n):
        r = Poly.const(1)
        for _ in range(n):
            r = r * self
        return r

    def iszero(self):
        return not self.d

    def subs(self, name, val):
        """Substitute a polynomial for a variable (nonnegative exponents only)."""
        i = IDX[name]
        out = Poly()
        cache = {}
        for k, v in self.d.items():
            e = k[i]
            if e < 0:
                raise ValueError('negative exponent substitution')
            if e not in cache:
                cache[e] = val ** e
            kk = list(k)
            kk[i] = 0
            out = out + Poly({tuple(kk): v}) * cache[e]
        return out

    def deriv(self, name):
        i = IDX[name]
        r = {}
        for k, v in self.d.items():
            if k[i] != 0:
                kk = list(k)
                kk[i] -= 1
                r[tuple(kk)] = r.get(tuple(kk), 0) + v * k[i]
        return Poly(r)

    def min_exp(self, name):
        i = IDX[name]
        return min((k[i] for k in self.d), default=0)

    def has_negative(self):
        return any(e < 0 for k in self.d for e in k)

    def uses(self):
        return {VARS[i] for k in self.d for i, e in enumerate(k) if e}

    def div_monomial(self, name, e):
        i = IDX[name]
        r = {}
        for k, v in self.d.items():
            kk = list(k)
            kk[i] -= e
            r[tuple(kk)] = v
        return Poly(r)


V = Poly.var
checks = {}
CLEAR = {}


def record(name, ok):
    if not ok:
        raise AssertionError(name)
    checks[name] = checks.get(name, 0) + 1


def derivation(values):
    """Return a derivation on polynomials determined by its values on variables."""
    def D(f):
        out = Poly()
        for name, val in values.items():
            df = f.deriv(name)
            if not df.iszero():
                out = out + df * val
        return out
    return D


def per_n(n):
    p, s, u, F, J, w = (V(k) for k in 'p s u F J w'.split())
    pn = p ** n
    x = s ** 2 + u ** 3 + pn * F
    y = s + x * (x - u ** 3)
    z = s * x + pn * J
    H = x ** 2 * F - (1 + 2 * s * x) * J - pn * J ** 2 - p * u
    Htop = H + p * u
    # (2.1)
    record('2.1 xy-z(z+1)=p^n(H+pu)', (x * y - z * (z + 1) - pn * (H + p * u)).iszero())

    # Delta on P: values from the candidate; check it kills x,y,z and Delta H = p^(n+1)
    Dl = derivation({'p': Poly(), 'u': -pn, 's': -3 * pn * x * u ** 2,
                     'F': (6 * s * x + 3) * u ** 2, 'J': 3 * x ** 2 * u ** 2})
    record('2.2 Delta x=y=z=0', Dl(x).iszero() and Dl(y).iszero() and Dl(z).iszero())
    DH = Dl(H)
    record('2.2 Delta H=p^(n+1)', (DH - p ** (n + 1)).iszero())
    record('2.2 Delta^2 H=0', Dl(DH).iszero())
    # exp(w Delta)(H)=H+p^(n+1) w follows from the two lines above.

    # Linear change and expansion
    x0 = s ** 2 + u ** 3
    Lv, Mv = V('L'), V('M')
    det = x0 ** 2 * 4 * s ** 2 + (1 + 2 * s * x0) * (1 - 2 * s * x0)
    record('2 determinant one', (det - 1).iszero())
    FL = 4 * s ** 2 * Lv + (1 + 2 * s * x0) * Mv
    JL = -(1 - 2 * s * x0) * Lv + x0 ** 2 * Mv
    record('2 inverse L', (x0 ** 2 * FL - (1 + 2 * s * x0) * JL - Lv).iszero())
    record('2 inverse M', ((1 - 2 * s * x0) * FL + 4 * s ** 2 * JL - Mv).iszero())
    HL = H.subs('F', FL).subs('J', JL)
    Q = 2 * x0 * FL ** 2 - 2 * s * FL * JL - JL ** 2
    record('2 H(L) expansion', (HL - (Lv - p * u + pn * Q + p ** (2 * n) * FL ** 3)).iszero())
    C = Q.subs('L', Poly())
    QmC = Q - C
    record('2 Q-C divisible by L', QmC.min_exp('L') >= 1)
    Q1 = QmC.div_monomial('L', 1)
    record('2 L*Q1=Q-C', (Lv * Q1 - QmC).iszero())
    Ls = p * u - pn * C
    HLs = HL.subs('L', Ls)
    rhs23 = p ** (n + 1) * ((u - p ** (n - 1) * C) * Q1.subs('L', Ls)
                            + p ** (n - 1) * FL.subs('L', Ls) ** 3)
    record('2.3 H(L_*) identity', (HLs - rhs23).iszero())
    h = u - p ** (n - 1) * Q - p ** (2 * n - 1) * FL ** 3 - pn * w
    record('2 H+p^(n+1)w=L-ph', (HL + p ** (n + 1) * w - (Lv - p * h)).iszero())
    e0 = -w - p ** (n - 1) * FL ** 3 - Q1 * h
    lhs = p ** (n + 1) * e0 - (Lv - Ls)
    rhs = (pn * Q1 - 1) * (HL + p ** (n + 1) * w)
    record('2.4 e-certificate', (lhs - rhs).iszero())
    Zv = V('Z')
    Wnum = HL.subs('L', Ls + p ** (n + 1) * Zv)
    record('2 W(Z) in B[Z]: p^(n+1) divides H(L_*+p^(n+1)Z)', Wnum.min_exp('p') >= n + 1
           and all(k[IDX['p']] >= n + 1 for k in Wnum.d))
    record('2 B-variables only in W', Wnum.uses() <= {'p', 's', 'u', 'M', 'Z'})

    # Section 3: initial forms. Work in Laurent coordinates (p,x,y,z,u).
    X, Y, Zc = V('x'), V('y'), V('z')
    sR = Y - X * (X - u ** 3)
    Floc = (X - sR ** 2 - u ** 3) * Poly.var('p', -n)
    Jloc = (Zc - sR * X) * Poly.var('p', -n)
    # substitute into x,y,z formulas to recover coordinates
    def to_loc(f):
        # f polynomial in p,s,u,F,J -> Laurent in p,x,y,z,u
        out = Poly()
        for k, v in f.d.items():
            term = Poly.const(v)
            for name, val in (('p', p), ('s', sR), ('u', u), ('F', Floc), ('J', Jloc)):
                e = k[IDX[name]]
                if e:
                    term = term * (val ** e)
            out = out + term
        return out
    record('3 inverse coordinates x', (to_loc(x) - X).iszero())
    record('3 inverse coordinates y', (to_loc(y) - Y).iszero())
    record('3 inverse coordinates z', (to_loc(z) - Zc).iszero())
    Hloc = to_loc(H)
    record('3 localized H', (Hloc - ((X * Y - Zc * (Zc + 1)) * Poly.var('p', -n) - p * u)).iszero())
    Srel = X * Y - Zc * (Zc + 1) - p ** (n + 1) * u
    record('3 S relation maps to p^n H', (to_loc(x * y - z * (z + 1) - p ** (n + 1) * u) - pn * Hloc).iszero())
    record('3 H_top localized', (to_loc(Htop) - (X * Y - Zc * (Zc + 1)) * Poly.var('p', -n)).iszero())
    # weight homogeneity of H_top under (-1,0,0,n,n)
    wt = {'p': -1, 's': 0, 'u': 0, 'F': n, 'J': n}
    weights = {sum(k[IDX[v]] * wt[v] for v in wt) for k in Htop.d}
    record('3 H_top homogeneous of weight n', weights == {n})
    record('3 x weight zero', {sum(k[IDX[v]] * wt[v] for v in wt) for k in x.d} == {0})
    # Jacobian at p=0
    dF = Htop.deriv('F').subs('p', Poly())
    dJ = Htop.deriv('J').subs('p', Poly())
    record('3 dH_top/dF at p=0 = x0^2', (dF - x0 ** 2).iszero())
    record('3 dH_top/dJ at p=0 = -(1+2s x0)', (dJ + (1 + 2 * s * x0)).iszero())
    record('3 H mod p', (H.subs('p', Poly()) - (x0 ** 2 * F - (1 + 2 * s * x0) * J)).iszero())

    # Section 5: DK lower inclusion; delta_1 on S
    d1 = derivation({'p': Poly(), 'x': Poly(), 'u': Poly(), 'z': X, 'y': 2 * Zc + 1})
    record('5 delta1 kills S relation', d1(Srel).iszero())
    record('5 delta1 s', (d1(sR) - (2 * Zc + 1)).iszero())
    record('5 delta1 F', (d1(Floc) - (-2 * sR * (2 * Zc + 1)) * Poly.var('p', -n)).iszero())
    record('5 delta1 J', (d1(Jloc) - (-2 * X * Zc) * Poly.var('p', -n)).iszero())
    # p^n delta1 maps generators into A: express values back in P
    record('5 p^n delta1 F in A', (pn * d1(Floc) - to_loc(-2 * s * (2 * z + 1))).iszero())
    record('5 p^n delta1 J in A', (pn * d1(Jloc) - to_loc(-2 * x * z)).iszero())
    # Coordinate partials of C[p^+-,x,y,z]=A[1/p]. There u=(xy-z(z+1))/p^(n+1) is not free,
    # so in (p,x,y,z,u)-coordinates the partial carries a chain-rule u-term.
    pinv = Poly.var('p', -(n + 1))
    partials = {'x': derivation({'x': Poly.const(1), 'u': Y * pinv}),
                'y': derivation({'y': Poly.const(1), 'u': X * pinv}),
                'z': derivation({'z': Poly.const(1), 'u': -(2 * Zc + 1) * pinv})}
    for var, Dv in partials.items():
        record('5 partial ' + var + ' kills S relation', Dv(Srel).iszero())
        vals = [Dv(g) for g in (sR, u, Floc, Jloc)]
        need = max(-dv.min_exp('p') for dv in vals if not dv.iszero())
        # p^need * value has no negative p-power, hence lies in S, a subring of A
        record('5 partial ' + var + ' clears with p^(2n+1)', need == 2 * n + 1)
        CLEAR[(n, var)] = need
    # residues p^nF, p^nJ -> f, g ; s -> s_R  (already polynomial in S)
    record('7 p^nF in S', not (pn * Floc).has_negative())
    record('7 p^nJ in S', not (pn * Jloc).has_negative())


def principalization():
    a, b, c, d, u = (V(k) for k in 'a b c d u'.split())
    x, y, z = a * b, d * c, d * b
    sR = y - x * (x - u ** 3)
    f = x - sR ** 2 - u ** 3
    g = z - sR * x
    v = a ** 3 * b - a ** 2 * u ** 3 - d ** 2
    hh = x - u ** 3
    C1 = c ** 2 - b ** 2 * hh
    al = a ** 2 * (1 - 2 * b * d)
    be = d ** 2 * (3 + 2 * b * d) + al * hh
    ainv = Poly.var('a', -1)
    cc = (1 + b * d) * ainv

    def red(P):
        # substitute c=(1+bd)/a in Laurent ring C[a^+-,b,d,u] = R~[1/a]
        out = Poly()
        for k, val in P.d.items():
            e = k[IDX['c']]
            kk = list(k)
            kk[IDX['c']] = 0
            out = out + Poly({tuple(kk): val}) * cc ** e
        return out
    record('4 xy=z(z+1) in R~', red(x * y - z * (z + 1)).iszero())
    record('4 f=C1 v', red(f - C1 * v).iszero())
    record('4 g=b^2 v', red(g - b ** 2 * v).iszero())
    record('4 v=alpha f+beta g', red(v - (al * f + be * g)).iszero())
    # fiber weights of v
    wts = {'a': 1, 'd': 1, 'b': -1, 'c': -1, 'u': 0}
    record('4 wt(v)=2', {sum(k[IDX[q]] * wts[q] for q in wts) for k in v.d} == {2})


def quotient_R_mod_I():
    s, u = V('s'), V('u')
    x = s ** 2 + u ** 3
    z = s * x
    y = s + x * (x - u ** 3)
    record('7 point satisfies xy=z(z+1)', (x * y - z * (z + 1)).iszero())
    sR = y - x * (x - u ** 3)
    record('7 s_R maps to s', (sR - s).iszero())
    record('7 f maps to 0', (x - sR ** 2 - u ** 3).iszero())
    record('7 g maps to 0', (z - sR * x).iszero())


def combinatorics():
    for n in range(2, 40):
        # (4.1): monomials tau^i V^h of degree e = n h - i reduce to the stated piece
        for e in range(-30, 60):
            for hdeg in range(0, 40):
                i = n * hdeg - e
                if i < 0:
                    continue
                if e <= 0:
                    ok = (i - n * hdeg == -e) and hdeg >= 0
                else:
                    q = -(-e // n)
                    ok = hdeg >= q and (i - n * (hdeg - q) == n * q - e) and n * q - e >= 0
                record('4.1 homogeneous pieces', ok)
        # Case 2: delta(tau) not in tau G~ forces j-1 = n q, and pieces for r in R~
        for jm1 in range(-20, 60):
            if jm1 < 0:
                in_tau = True
            else:
                q = -(-jm1 // n) if jm1 > 0 else 0
                in_tau = (n * q - jm1) >= 1
            record('4 case-2 shift', in_tau == (jm1 < 0 or jm1 % n != 0))
            if jm1 >= 0 and jm1 % n == 0:
                j = jm1 + 1
                qq = -(-j // n)
                record('4.2 tau^(n-1) V^(q+1)', qq == jm1 // n + 1 and n * qq - j == n - 1)
        for m in range(1, 200):
            nu_Ev = n * m - 1 - (n - 1) * m
            record('4.3 nu(E v)=m-1', nu_Ev == m - 1)
            record('4.3 E^2 v order negative', nu_Ev - 1 - (n - 1) * m < 0)
        # (7.1): degree-r part of R[tau, I/tau^n] has coefficient ideal I^ceil(r/n)
        for r in range(1, 200):
            ks = [k for k in range(0, 400) if n * k - r >= 0]
            k0 = -(-r // n)
            record('7.1 minimal power', min(ks) == k0)
            record('7.2 staircase index', (k0 == 1) == (r <= n))
    # n=1 would fail the order step (documented boundary)
    record('boundary n=1 order step fails for m>=2', (2 - 1) * 2 - 2 >= 0)


def main():
    for n in range(2, NMAX + 1):
        per_n(n)
    principalization()
    quotient_R_mod_I()
    combinatorics()
    print(json.dumps({'status': 'PASS_EXACT_FINITE_IDENTITY_CHECKS', 'n_range': [2, NMAX],
                      'distinct_checks': len(checks), 'total_assertions': sum(checks.values()),
                      'coordinate_partial_clearing_exponent_on_generators': sorted({v for v in CLEAR.values()}),
                      'clearing_rule': '2n+1 for every n in range and every partial x,y,z',
                      'limit': 'Finite exact identities only; no theorem, LND classification or geometry is certified.'},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except AssertionError as e:
        print('FAIL: ' + str(e), file=sys.stderr)
        sys.exit(1)
