# Independent checker "F" for nd-sym certificates (stdlib only).  Written from notes/highdim_sym.md and first principles.
# [F5] extension of check_sym_F.py: pin_digits = k is accepted for 1 <= k <= qmin
# (was k <= min(3, qmin)).  Soundness: on the domain every position (and L) is >= qmin >= k,
# so X == K (mod 10^k) and Y = X/2^t0 == K0 (mod 5^k * 2^max(k-t0,0)) — dividing by 2^t0 exactly once.
# Because A*W ~ 24*25^(k-1) for deep pins, the naive enumeration of all (a mod A, w mod W)
# pairs is replaced by an exact coset/lattice solver (see _solve_free/_solve_gx below);
# the allowed residue set at a prime p is unchanged (verified by test_F5.py against
# check_sym_F_base.py, a verbatim copy of check_sym_F.py).
# usage: python3 -I check_sym_F5.py cert.jsonl [brute_Lmax=11] [--json]
#
# CLAIM being certified (scope "full", domain "unordered"):
#   for all L, and all pairwise-distinct positions q (one per slot of the groups [c_g, m_g]) with qmin <= q < L,
#       X = 10^L + sum_g c_g * sum_{slots of g} 10^q + K   is NOT of the form 2^t0 * 3^a * 7^w  (t0 = v2(K)),
#   except for the points listed in the 'sz' leaves.
# Mathematical facts used (proved in REPORT_F.md):
#   (V2)  qmin > t0  =>  v2(X) = t0.
#   (SIG) 3-adic / 7-adic signature of a class mod M.
#   (AL)  aligned prime kill, (SS) sumset kill, (P2) mod-8 pin, (TL) decimal-tail coset pin, (SZ) size leaf.
import sys, json, itertools, collections
from math import gcd

# ---------------------------------------------------------------- number theory (self contained)
def v_p(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k

_pc = {}
def isprime(n):
    if n in _pc: return _pc[n]
    _pc[n] = _isprime(n)
    return _pc[n]

def _isprime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

_fc = {}
def factor(n):
    if n in _fc: return _fc[n]
    f = {}; m = n; q = 2
    while q * q <= m:
        while m % q == 0:
            f[q] = f.get(q, 0) + 1; m //= q
        q += 1 if q == 2 else 2
    if m > 1: f[m] = f.get(m, 0) + 1
    _fc[n] = f
    return f

def phi(n):
    r = n
    for q in factor(n): r = r // q * (q - 1)
    return r

_oc = {}
def order(a, n):
    """multiplicative order of a modulo n (gcd(a,n)=1)"""
    key = (a % n, n)
    if key in _oc: return _oc[key]
    assert n > 1 and gcd(a, n) == 1
    o = phi(n)
    for q in factor(o):
        while o % q == 0 and pow(a, o // q, n) == 1: o //= q
    _oc[key] = o
    return o

def lcm(a, b): return a // gcd(a, b) * b

# ---------------------------------------------------------------- weak compositions / lifts
def weak_comps(h, f):
    """all f-tuples of non-negative ints summing to h"""
    if f == 1:
        yield (h,); return
    for first in range(h + 1):
        for rest in weak_comps(h - first, f - 1):
            yield (first,) + rest

def group_lifts(res, M, f):
    """all sorted multisets (tuples) mod fM whose reduction mod M is the sorted multiset `res` (residues in [0,M))"""
    cnt = collections.Counter(res)
    blocks = []
    for b in sorted(cnt):
        h = cnt[b]
        blocks.append([tuple(b + i * M for i in range(f) for _ in range(c[i])) for c in weak_comps(h, f)])
    out = []
    for choice in itertools.product(*blocks):
        out.append(tuple(sorted(x for blk in choice for x in blk)))
    return out

def class_lifts(cls, M, f):
    L, grps = cls[0], cls[1:]
    Ls = [L + i * M for i in range(f)]
    gl = [group_lifts(g, M, f) for g in grps]
    for l in Ls:
        for combo in itertools.product(*gl):
            yield (l,) + combo

# ---------------------------------------------------------------- [F5] deep-pin arithmetic
# The pin congruence is 3^a 7^w == K0 (mod E) with E = 2^e2 * 5^e5 (K0 = K/2^t0, odd).
# Structure used (all verified in test_F5.py):
#   mod 5^e5:  3 is a primitive root (ord = 4*5^(e5-1)); 7 = 3^s5, K0 = 3^u5, so the
#              congruence becomes the linear relation a + s5*w == u5 (mod 4*5^(e5-1));
#   mod 2^e2:  <3> = {units == 1 or 3 mod 8}, ord_{2^e2}(3) = 2^(e2-2) (e2 >= 3), and
#              7 = -3^s2, so 3^a 7^w = (-1)^w 3^(a + s2*w): the congruence becomes
#              w == wpar (mod 2) and a + s2*w == u2 (mod 2^(e2-2));  for e2 = 2 one has
#              7 == 3 (mod 4) and the single relation a + w == u2 (mod 2);  e2 <= 1 is vacuous.
# The admissible exponent set is therefore a coset of a rank-2 lattice; its image under
# (a,w) |-> 3^a 7^w (mod p) is rep * <3^ga 7^gw (mod p)>, tested with ONE exponentiation
# per sumset element.  This equals the union of cosets of the old enumeration exactly.

def _crt2(r1, m1, r2, m2):
    """[F5] combine x == r1 (mod m1), x == r2 (mod m2); returns (r, lcm) or None."""
    g = gcd(m1, m2)
    if (r2 - r1) % g: return None
    l = m1 // g * m2
    q = m2 // g
    t = (r2 - r1) // g * pow(m1 // g, -1, q) % q if q > 1 else 0
    return ((r1 + m1 * t) % l, l)

def _crt_aff(m, c, d, m2, c2, d2):
    """[F5] combine f == c + d*x (mod m) with f == c2 + d2*x (mod m2); (lcm, c, d) or None."""
    g = gcd(m, m2)
    if (c2 - c) % g or (d2 - d) % g: return None
    r = _crt2(c % m, m, c2 % m2, m2)
    if r is None: return None
    s = _crt2(d % m, m, d2 % m2, m2)
    if s is None: return None
    return (r[1], r[0] % r[1], s[0] % s[1])

def _dlog3_5k(h, k):
    """[F5] x with 3^x == h (mod 5^k), 0 <= x < 4*5^(k-1); None if 5 | h.  k >= 1.
    Pohlig-Hellman: x mod 4 through 3^(5^(k-1)) (order 4), x mod 5^(k-1) digit-by-digit
    through (3^4)^x with 3^4 of order 5^(k-1)."""
    if h % 5 == 0: return None
    m = 5 ** k
    gam = pow(3, m // 5, m)                                   # order 4
    x4 = next(i for i in range(4) if pow(gam, i, m) == pow(h, m // 5, m))
    x5 = 0
    if k > 1:
        g4 = pow(3, 4, m)                                     # order 5^(k-1)
        h4 = pow(h, 4, m)
        gam5 = pow(g4, 5 ** (k - 2), m)                       # order 5
        for i in range(k - 1):
            t = pow(h4 * pow(g4, -x5, m) % m, 5 ** (k - 2 - i), m)
            x5 += next(j for j in range(5) if pow(gam5, j, m) == t) * 5 ** i
    return _crt2(x4, 4, x5, 5 ** (k - 1))[0]

def _dlog3_2j(t, j):
    """[F5] x with 3^x == t (mod 2^j), for t == 1 or 3 (mod 8); j >= 3.  x in [0, 2^(j-2)).
    Bit-by-bit: 3^(2^(j-3)) has order 2."""
    x = 0
    gam = pow(3, 2 ** (j - 3), 2 ** j)                        # order 2
    for i in range(j - 2):
        tt = pow(t * pow(3, -x, 2 ** j) % (2 ** j), 2 ** (j - 3 - i), 2 ** j)
        assert tt == 1 or tt == gam, "dlog3_2j: target not in <3>"
        x += (0 if tt == 1 else 1) << i
    return x

# ---------------------------------------------------------------- certificate context
class Cert:
    def __init__(self, meta):
        self.problems = []
        m = meta
        if m.get('k') != 'meta' or m.get('format') != 'nd-sym' or m.get('version') != 1: self.bad("meta: format")
        if m.get('domain') != 'unordered': self.bad("domain must be unordered")
        if m.get('scope') != 'full': self.bad("scope must be full")
        self.coefs = [g[0] for g in m['groups']]
        self.mult = [g[1] for g in m['groups']]
        if len(set(self.coefs)) != len(self.coefs) or any(c <= 0 for c in self.coefs) or any(m < 1 for m in self.mult): self.bad("groups")
        self.K, self.qmin = m['K'], m['qmin']
        self.F = sum(self.mult)
        if m['dim'] != 1 + self.F: self.bad("dim")
        self.t0 = v_p(self.K, 2)
        if not (self.K > 0 and self.qmin > self.t0): self.bad("need K>0 and qmin>v2(K)")
        self.pin2 = bool(m.get('pin2'))
        if self.pin2 and self.qmin < self.t0 + 3: self.bad("pin2 requires qmin >= t0+3")
        pd = m.get('pin_digits')
        self.k = int(pd) if pd else 0
        if self.k and not (1 <= self.k <= self.qmin): self.bad("pin_digits out of range")   # [F5] was k <= min(3, qmin)
        self.root = m['root']
        if self.root['m'] != 1: self.bad("root modulus must be 1")
        self.rootcls = self.mkcls(self.root['r'])
        if self.rootcls is None or self.rootcls[0] != 0 or any(any(self.rootcls[1 + i]) for i in range(len(self.mult))): self.bad("root not all-zero")
        self.kt = self.K >> self.t0                # odd part of K
        # ---- pin constraint: 3^a 7^w == kt (mod E) for every point of the domain  (P2: mod 8, TL: mod 5^k 2^max(k-t0,0))
        e2 = 0; e5 = 0
        if self.pin2: e2 = 3
        if self.k: e2 = max(e2, max(self.k - self.t0, 0)); e5 = self.k
        self.E = 2 ** e2 * 5 ** e5
        self._ps = {}; self._admc = {}           # [F5] caches for the structured pin solver (replaces _pairs)
        self.killcache = {}
        self.powcache = {}
        self.stats = collections.Counter()
        self.kinds = collections.Counter()      # kinds of verified kills (per verified lift) and per unique kill
        self.ukinds = collections.Counter()

    def bad(self, s):
        if len(self.problems) < 40: self.problems.append(s)

    def mkcls(self, r):
        """validate a node residue [L,[g1],[g2],...] -> canonical tuple or None"""
        if not (isinstance(r, list) and len(r) == 1 + len(self.mult)): return None
        if not isinstance(r[0], int): return None
        out = [r[0]]
        for g, mm in zip(r[1:], self.mult):
            if not (isinstance(g, list) and len(g) == mm and all(isinstance(x, int) for x in g)): return None
            if g != sorted(g): return None
            out.append(tuple(g))
        return tuple(out)

    # ---- exact value of X mod n using residues (only valid when ord_n(10) | M)
    def xmod(self, cls, n):
        s = pow(10, cls[0], n) + self.K
        for c, g in zip(self.coefs, cls[1:]):
            for r in g: s += c * pow(10, r, n)
        return s % n

    def sig(self, cls, M):
        """(a0, a_exact, w0, w_exact): from the class mod M: v3(X)=a0 exactly, or a>=a0 (SIG)"""
        j = v_p(M, 3); m3 = 3 ** (j + 2)
        assert pow(10, 3 ** j, m3) == 1 and M % (3 ** j) == 0
        x = self.xmod(cls, m3)
        a = (j + 2, False) if x == 0 else (v_p(x, 3), True)
        if M % 6 == 0:
            i = v_p(M, 7); m7 = 7 ** (i + 1)
            assert pow(10, 6 * 7 ** i, m7) == 1 and M % (6 * 7 ** i) == 0
            x = self.xmod(cls, m7)
            w = (i + 1, False) if x == 0 else (v_p(x, 7), True)
        else:
            w = (0, False)
        return a[0], a[1], w[0], w[1]

    # ---- [F5] structured admissible exponent set for the pin congruence
    def _pinstruct(self, E):
        """[F5] cached dlog structure of the unit group mod E = 2^e2 * 5^e5."""
        v = self._ps.get(E)
        if v is None:
            e2 = v_p(E, 2); e5 = v_p(E, 5)
            v = {'e2': e2, 'e5': e5}
            if e5:
                v['A5'] = 4 * 5 ** (e5 - 1)                    # ord_{5^e5}(3): 3 is a primitive root
                v['s5'] = _dlog3_5k(7 % 5 ** e5, e5)           # 7 == 3^s5 (mod 5^e5)
            if e2 >= 2:
                if e2 == 2:
                    v['A2'] = 2; v['s2'] = 1                   # 7 == 3 (mod 4)
                else:
                    v['A2'] = 2 ** (e2 - 2)                    # ord_{2^e2}(3)
                    v['s2'] = _dlog3_2j((-7) % 2 ** e2, e2)    # 7 == -3^s2 (mod 2^e2)
            self._ps[E] = v
        return v

    def _solve_gx(self, E, g, h):
        """[F5] solve g^x == h (mod E) for g in {3,7}, h odd, E = 2^e2*5^e5 > 2.
        Returns (x, M) with solution set x + M*Z, or None if unsolvable."""
        ps = self._pinstruct(E)
        x, M = 0, 1
        if ps['e2'] >= 1 and h % 2 == 0: return None    # [F5] g^x is odd, h is not
        if ps['e5']:
            if h % 5 == 0: return None
            A5, s5 = ps['A5'], ps['s5']
            u = _dlog3_5k(h % 5 ** ps['e5'], ps['e5'])         # g^x == h  <=>  s5*x == u (mod A5) for g = 7; s5 = 1 for g = 3
            if g == 3: s5 = 1
            dd = gcd(s5, A5)
            if u % dd: return None
            r = _crt2(x, M, u // dd * pow(s5 // dd, -1, A5 // dd) % (A5 // dd), A5 // dd)
            if r is None: return None
            x, M = r
        e2 = ps['e2']
        if e2 >= 2:
            A2, s2 = ps['A2'], ps['s2']
            if e2 == 2:
                r = _crt2(x, M, 0 if h % 4 == 1 else 1, 2)     # g == 3 (mod 4), period 2
            elif g == 3:
                if h % 8 not in (1, 3): return None            # 3^x mod 2^e2 in <3> = {1,3 mod 8}
                r = _crt2(x, M, _dlog3_2j(h % 2 ** e2, e2), A2)
            else:
                if h % 8 in (1, 3): par, u = 0, _dlog3_2j(h % 2 ** e2, e2)
                else: par, u = 1, _dlog3_2j((-h) % 2 ** e2, e2)   # 7^x = (-1)^x 3^(s2 x)
                dd = gcd(s2, A2)
                if u % dd: return None
                r1 = _crt2(u // dd * pow(s2 // dd, -1, A2 // dd) % (A2 // dd), A2 // dd, par, 2)
                if r1 is None: return None
                r = _crt2(x, M, r1[0], r1[1])
            if r is None: return None
            x, M = r
        return (x, M)

    def _solve_free(self, E):
        """[F5] solution set of 3^a 7^w == K0 (mod E), both exponents free.
        Returns ((ap, wp), gens): the set is (ap,wp) + lattice(gens); None if empty."""
        ps = self._pinstruct(E)
        tau = self.kt % E
        if ps['e2'] >= 1 and tau % 2 == 0: return None  # [F5] 3^a 7^w is odd, tau is not
        u5 = u2 = wpar = None
        if ps['e5']:
            if tau % 5 == 0: return None               # 3^a 7^w is a unit mod 5, K0 is not
            u5 = _dlog3_5k(tau % 5 ** ps['e5'], ps['e5'])
        if ps['e2'] >= 3:
            wpar = 0 if tau % 8 in (1, 3) else 1       # sign of 7^w forced by K0 mod 8
            tgt = tau % 2 ** ps['e2'] if wpar == 0 else (-tau) % 2 ** ps['e2']
            u2 = _dlog3_2j(tgt, ps['e2'])
        elif ps['e2'] == 2:
            u2 = 0 if tau % 4 == 1 else 1
        # constraints on w alone: the sign parity, and the compatibility of the two
        # relations a == u5 - s5*w (A5) and a == u2 - s2*w (A2), i.e. mod gcd(A5, A2)
        wc = []
        if wpar is not None: wc.append((wpar, 2))
        if u5 is not None and u2 is not None:
            g25 = gcd(ps['A5'], ps['A2'])
            c = (ps['s2'] - ps['s5']) % g25; r = (u2 - u5) % g25
            dd = gcd(c, g25)
            if r % dd: return None
            wc.append((r // dd * pow(c // dd, -1, g25 // dd) % (g25 // dd), g25 // dd))
        w, Mw = 0, 1
        for r, m in wc:
            rr = _crt2(w, Mw, r, m)
            if rr is None: return None
            w, Mw = rr
        # a == g0 + gt*t (mod A) with w == w* + Mw*t
        A, g0, gt = 1, 0, 0
        if u5 is not None:
            s5 = ps['s5']
            r = _crt_aff(A, g0, gt, ps['A5'], (u5 - s5 * w) % ps['A5'], (-s5 * Mw) % ps['A5'])
            if r is None: return None               # cannot happen: compatibility enforced above
            A, g0, gt = r
        if u2 is not None:
            s2 = ps['s2']
            r = _crt_aff(A, g0, gt, ps['A2'], (u2 - s2 * w) % ps['A2'], (-s2 * Mw) % ps['A2'])
            if r is None: return None               # cannot happen: compatibility enforced above
            A, g0, gt = r
        return ((g0 % A, w), [(gt, Mw), (A, 0)])

    def _solve_pair(self, E, sg):
        """[F5] admissible exponent set for pin modulus E and signature sg = (a0, aex, w0, wex).
        Returns ((ra, rw), gens): the allowed residues at a prime p are
        3^ra 7^rw * <3^ga 7^gw (mod p) : (ga,gw) in gens>;  None if the set is empty."""
        a0, aex, w0, wex = sg
        if E <= 2:
            # [F5] congruence mod 1 or 2 is vacuous (K0 odd)
            if aex and wex: return ((a0, w0), [])
            if aex: return ((a0, 0), [(0, 1)])
            if wex: return ((0, w0), [(1, 0)])
            return ((0, 0), [(1, 0), (0, 1)])
        if aex and wex:
            return ((a0, w0), []) if pow(3, a0, E) * pow(7, w0, E) % E == self.kt % E else None
        if aex:                                         # a fixed to a0: solve 7^w == K0 * 3^-a0 (mod E)
            h = self.kt * pow(pow(3, a0, E), -1, E) % E
            r = self._solve_gx(E, 7, h)
            return None if r is None else ((a0, r[0]), [(0, r[1])])
        if wex:                                         # w fixed to w0: solve 3^a == K0 * 7^-w0 (mod E)
            h = self.kt * pow(pow(7, w0, E), -1, E) % E
            r = self._solve_gx(E, 3, h)
            return None if r is None else ((r[0], w0), [(r[1], 0)])
        return self._solve_free(E)

    def Eset(self, variant):
        """modulus used by pin variant: 'plain','p2','tail','both'"""
        e2 = 0; e5 = 0
        if self.pin2 and variant in ('p2', 'both'): e2 = 3
        if self.k and variant in ('tail', 'both'):
            e2 = max(e2, max(self.k - self.t0, 0)); e5 = self.k
        return 2 ** e2 * 5 ** e5

    def sset(self, p, d, g, r):
        key = (p, g, r)
        s = self.powcache.get(key)
        if s is None:
            s = frozenset(pow(10, e, p) for e in range(r, d, g))
            self.powcache[key] = s
        return s

    def sumset(self, p, d, g, redcls):
        """set of all values of X mod p over residue tuples q (mod d) compatible with the class mod g  (SS)"""
        cur = {(self.K + s) % p for s in self.sset(p, d, g, redcls[0])}
        for c, grp in zip(self.coefs, redcls[1:]):
            for r in grp:
                S = [(c * s) % p for s in self.sset(p, d, g, r)]
                if len(S) == 1:
                    s0 = S[0]; cur = {(x + s0) % p for x in cur}
                else:
                    cur = {(x + s) % p for x in cur for s in S}
                if len(cur) > 3_000_000: raise OverflowError("sumset too large")
        return cur

    def kill_variant(self, p, M, d, g, redcls, sg, variant):
        E = self.Eset(variant)
        rep, nU = self._adm(p, E, sg)                # [F5] replaces the (A, W, P) pair enumeration
        if rep is None: return True                  # [F5] no admissible exponent pair at all
        inv2 = pow(2, -self.t0, p) if self.t0 else 1
        T = pow(rep, nU, p)                          # [F5] allowed set is the single coset rep*<gens>
        for s in self.sumset(p, d, g, redcls):
            if pow(s * inv2 % p, nU, p) == T: return False
        return True

    def _adm(self, p, E, sg):
        """[F5] (rep, nU): allowed residues mod p are exactly {y : y^nU == rep^nU};
        (None, None) if no exponent pair is admissible."""
        key = (p, E, sg)
        v = self._admc.get(key)
        if v is None:
            sol = self._solve_pair(E, sg)
            if sol is None: v = (None, None)
            else:
                (ra, rw), gens = sol
                nU = 1
                for ga, gw in gens:
                    x = pow(3, ga, p) * pow(7, gw, p) % p
                    if x != 1: nU = lcm(nU, order(x, p))
                v = (pow(3, ra, p) * pow(7, rw, p) % p, nU)
            self._admc[key] = v
        return v

    def kills(self, p, cls, M, sg=None):
        """True iff prime p kills the class `cls` mod M.  Returns (bool, kind)."""
        assert isprime(p) and p > 7, "bad prime"
        d = order(10, p); g = gcd(d, M)
        if sg is None: sg = self.sig(cls, M)
        red = (cls[0] % g,) + tuple(tuple(sorted(r % g for r in grp)) for grp in cls[1:])
        key = (p, g, sg, red)
        v = self.killcache.get(key)
        if v is None:
            if self.kill_variant(p, M, d, g, red, sg, 'both'):
                kind = None
                for var in ('plain', 'p2', 'tail', 'both'):
                    if var == 'p2' and not self.pin2: continue
                    if var == 'tail' and not self.k: continue
                    if var == 'both' and not (self.pin2 and self.k): continue
                    if self.kill_variant(p, M, d, g, red, sg, var): kind = var; break
                v = (True, ('aligned' if d == g else 'sumset') + '/' + kind)
                self.ukinds[v[1]] += 1
            else:
                v = (False, None)
            self.killcache[key] = v
        return v

# ---------------------------------------------------------------- DFS for exact solutions of X = N inside a class
def solutions_N(ct, N):
    """all domain points (L, groups-of-positions) with X == N.  Domain: positions pairwise distinct, qmin<=q<L."""
    coefs, mult = ct.coefs, ct.mult
    sols = []
    pass
    def ub(counts, q):   # max of sum over remaining slots with positions < q (strictly decreasing)
        items = sorted(((c, n) for c, n in zip(coefs, counts) if n), reverse=True)
        tot = 0; pos = q - 1
        for c, n in items:
            for _ in range(n):
                tot += c * 10 ** pos; pos -= 1
        return tot
    def dfs(R, qx, counts, placed, L):
        if not any(counts):
            if R == 0: sols.append((L, [sorted(x for x in placed[i]) for i in range(len(coefs))]))
            return
        need = sum(counts)
        for q in range(qx - 1, ct.qmin - 1, -1):
            if q - ct.qmin + 1 < need: break
            any_alive = False
            for i, c in enumerate(coefs):
                if not counts[i]: continue
                rem = R - c * 10 ** q
                if rem < 0: continue
                counts[i] -= 1
                u = ub(counts, q) if any(counts) else 0
                ok = rem <= u
                if ok:
                    any_alive = True
                    placed[i].append(q); dfs(rem, q, counts, placed, L); placed[i].pop()
                counts[i] += 1
            # if R already exceeds what remains for every coefficient choice at this q, lower q cannot help
            if not any_alive:
                best_rem = min((R - c * 10 ** q) for i, c in enumerate(coefs) if counts[i])
                if best_rem > 0 and all((R - c * 10 ** q) > 0 for i, c in enumerate(coefs) if counts[i]):
                    # all choices left a positive remainder above the bound: smaller q only increases the remainder
                    break
    L = ct.qmin + (1 if ct.F else 0)      # dim 1 (no slots): domain is L >= qmin
    while True:
        base = 10 ** L + ct.K + sum(c * m * 10 ** ct.qmin for c, m in zip(coefs, mult))  # crude lower bound on X for this L
        if base > N: break
        R = N - ct.K - 10 ** L
        if R >= 0:
            dfs(R, L, list(mult), [[] for _ in coefs], L)
        L += 1
    return sols

def flat(L, groups):
    return [L] + [q for g in groups for q in sorted(g)]

def cls_of_point(ct, L, groups, M):
    return (L % M,) + tuple(tuple(sorted(q % M for q in g)) for g in groups)

# ---------------------------------------------------------------- tree verification
def check(path, BRUTE=11):
    raw = [json.loads(l) for l in open(path) if l.strip()]
    ct = Cert(raw[0])
    nodes = {}
    for n in raw[1:]:
        if n['id'] in nodes: ct.bad("duplicate id %s" % n['id'])
        nodes[n['id']] = n
    roots = [i for i, n in nodes.items() if n['p'] == -1]
    if len(roots) != 1: ct.bad("need exactly one root"); return ct, [], []
    visited = set(); claimed = []
    sys.setrecursionlimit(10000)

    def visit(i, cls, M, parent):
        if i not in nodes or i in visited: ct.bad("missing/duplicate/cyclic node %s" % i); return
        visited.add(i); nd = nodes[i]
        if nd['p'] != parent or nd['m'] != M or ct.mkcls(nd['r']) != cls: ct.bad("node %s header mismatch" % i); return
        if nd['k'] == 'l':
            ct.stats['leaves'] += 1
            x = nd['x']
            if 'prime' in x:
                ok, kind = ct.kills(x['prime'], cls, M)
                if ok: ct.stats['leaf_prime_ok'] += 1; ct.kinds['leaf/' + kind] += 1
                else: ct.bad("leaf %s: prime %s does not kill" % (i, x['prime']))
            elif 'sz' in x:
                a0, aex, w0, wex = ct.sig(cls, M)
                if not (aex and wex): ct.bad("leaf %s: sz needs exact a,w" % i); return
                if list(x['sz']) != [a0, w0]: ct.bad("leaf %s: sz exponents" % i); return
                N = 2 ** ct.t0 * 3 ** a0 * 7 ** w0
                mine = []
                for L, grps in solutions_N(ct, N):
                    if cls_of_point(ct, L, grps, M) == cls: mine.append(flat(L, grps))
                mine.sort()
                if mine != sorted(list(y) for y in x['sol']): ct.bad("leaf %s: sz solutions %s != declared %s" % (i, mine, x['sol']))
                else: ct.stats['leaf_sz_ok'] += 1
                claimed.extend(mine)
            else: ct.bad("leaf %s: unknown kill" % i)
            return
        if nd['k'] != 'i': ct.bad("node kind"); return
        M2 = nd['m2']
        if not (isinstance(M2, int) and M2 > M and M2 % M == 0): ct.bad("node %s: bad m2" % i); return
        f = M2 // M
        kids = {}
        for cid in nd['c']:
            if cid not in nodes: ct.bad("missing child %s" % cid); continue
            cc = ct.mkcls(nodes[cid]['r'])
            if cc is None or nodes[cid]['m'] != M2 or nodes[cid]['p'] != i: ct.bad("child %s header" % cid); continue
            if cc in kids: ct.bad("duplicate child class at %s" % i); continue
            if any(not (0 <= r < M2) for r in (cc[0],) + tuple(x for g in cc[1:] for x in g)): ct.bad("child residue range"); continue
            kids[cc] = cid
        rest = nd.get('rest') or []
        if isinstance(rest, int): rest = [rest]
        for p in rest:
            if not (isinstance(p, int) and isprime(p) and p > 7): ct.bad("node %s: rest prime %s invalid" % (i, p))
        lifts = set(); nl = 0
        for lf in class_lifts(cls, M, f):
            nl += 1
            lifts.add(lf) if lf in kids else None
            if lf in kids: continue
            ok = False
            sg = None
            for p in rest:
                if not (isinstance(p, int) and isprime(p) and p > 7): continue
                if sg is None: sg = ct.sig(lf, M2)
                good, kind = ct.kills(p, lf, M2, sg)
                if good: ok = True; ct.kinds['rest/' + kind] += 1; break
            if ok: ct.stats['rest_ok'] += 1
            else: ct.bad("node %s: lift %s mod %s neither child nor killed" % (i, lf, M2)); ct.stats['rest_FAIL'] += 1
        ct.stats['refinements'] += nl
        if set(kids) != lifts: ct.bad("node %s: explicit child is not a lift of the parent: %s" % (i, [k for k in kids if k not in lifts][:2]))
        for cc, cid in kids.items(): visit(cid, cc, M2, i)

    visit(roots[0], ct.rootcls, 1, -1)
    if len(visited) != len(nodes): ct.bad("unreachable nodes: %d" % (len(nodes) - len(visited)))

    # ---- brute box: every smooth point with L<=BRUTE must sit in a declared sz leaf; and no declared solution may be false
    def locate(L, groups):
        i = roots[0]
        while True:
            nd = nodes[i]
            if nd['k'] == 'l': return i
            M2 = nd['m2']
            key = cls_of_point(ct, L, groups, M2)
            nxt = None
            for c in nd['c']:
                if ct.mkcls(nodes[c]['r']) == key: nxt = c; break
            if nxt is None: return None
            i = nxt
    brute = []; npts = 0
    for L in range(ct.qmin + (1 if ct.F else 0), BRUTE + 1):
        pos = list(range(ct.qmin, L))
        if len(pos) < ct.F: continue
        # assign disjoint position subsets to groups
        def rec(gi, avail, acc):
            if gi == len(ct.coefs):
                yield list(acc); return
            for sub in itertools.combinations(avail, ct.mult[gi]):
                yield from rec(gi + 1, [x for x in avail if x not in sub], acc + [list(sub)])
        for groups in rec(0, pos, []):
            npts += 1
            X = 10 ** L + ct.K + sum(c * 10 ** q for c, g in zip(ct.coefs, groups) for q in g)
            if X % (1 << ct.t0) or (X >> ct.t0) % 2 == 0: continue
            Y = X >> ct.t0
            for pr in (3, 7):
                while Y % pr == 0: Y //= pr
            if Y == 1:
                brute.append(flat(L, groups))
                li = locate(L, groups)
                if li is None or 'sz' not in nodes[li].get('x', {}) or flat(L, groups) not in [list(y) for y in nodes[li]['x']['sol']]:
                    ct.bad("brute smooth point %s not recorded in an sz leaf" % (flat(L, groups),))
    ct.stats['brute_points'] = npts
    if sorted(brute) != sorted(c for c in claimed if c[0] <= BRUTE): ct.bad("claimed vs brute mismatch")
    return ct, claimed, brute

if __name__ == '__main__':
    path = sys.argv[1]
    BR = int(sys.argv[2]) if len(sys.argv) > 2 and not sys.argv[2].startswith('--') else 11
    try:
        ct, claimed, brute = check(path, BR)
    except Exception as e:      # malformed input = rejection
        print(json.dumps(dict(file=path, result='FAIL', problems=['exception %s: %s' % (type(e).__name__, e)]))); sys.exit(1)
    res = dict(file=path, result='FAIL' if ct.problems else 'PASS', K=ct.K, qmin=ct.qmin, dim=1 + ct.F, groups=list(zip(ct.coefs, ct.mult)),
               pin2=ct.pin2, pin_digits=ct.k, E=ct.E, stats=dict(ct.stats), kinds=dict(ct.kinds), ukinds=dict(ct.ukinds),
               claimed=claimed, brute=brute, problems=ct.problems[:10])
    if '--json' in sys.argv: print(json.dumps(res))
    else:
        print(path, res['result'], dict(ct.stats)); print('  kinds', dict(ct.kinds)); print('  claimed', claimed, 'brute', brute)
        for p in ct.problems[:10]: print('   -', p)
    sys.exit(1 if ct.problems else 0)
