# Independent checker "F" for nd-sym certificates (stdlib only).  Written from notes/highdim_sym.md and first principles.
# usage: python3 -I check_sym_F.py cert.jsonl [brute_Lmax=11] [--json]
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
        if len(set(self.coefs)) != len(self.coefs) or min(self.coefs) <= 0 or min(self.mult) < 1: self.bad("groups")
        self.K, self.qmin = m['K'], m['qmin']
        self.F = sum(self.mult)
        if m['dim'] != 1 + self.F: self.bad("dim")
        self.t0 = v_p(self.K, 2)
        if not (self.K > 0 and self.qmin > self.t0): self.bad("need K>0 and qmin>v2(K)")
        self.pin2 = bool(m.get('pin2'))
        if self.pin2 and self.qmin < self.t0 + 3: self.bad("pin2 requires qmin >= t0+3")
        pd = m.get('pin_digits')
        self.k = int(pd) if pd else 0
        if self.k and not (1 <= self.k <= min(3, self.qmin)): self.bad("pin_digits out of range")
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
        self._pairs = {}
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

    # ---- admissible (alpha mod A, beta mod W) pairs from the pin constraint
    def pairs(self, E):
        if E in self._pairs: return self._pairs[E]
        if E == 1: res = (1, 1, [(0, 0)])
        else:
            A, W = order(3, E), order(7, E)
            tau = self.kt % E
            P = [(al, be) for al in range(A) for be in range(W) if pow(3, al, E) * pow(7, be, E) % E == tau]
            res = (A, W, P)
        self._pairs[E] = res
        return res

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
        A, W, P = self.pairs(E)
        a0, aex, w0, wex = sg
        inv2 = pow(2, -self.t0, p) if self.t0 else 1
        h = []
        if not aex: h.append(pow(3, A, p))
        if not wex: h.append(pow(7, W, p))
        nH = 1
        for x in h: nH = lcm(nH, order(x, p))
        img = set()
        for al, be in P:
            if aex and (al - a0) % A: continue
            if wex and (be - w0) % W: continue
            ae = a0 if aex else al
            be_ = w0 if wex else be
            img.add(pow(pow(3, ae, p) * pow(7, be_, p) % p, nH, p))
        if not img: return True          # no admissible exponent pair at all
        for s in self.sumset(p, d, g, redcls):
            if pow(s * inv2 % p, nH, p) in img: return False
        return True

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
    cmin = min(coefs)
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
    L = ct.qmin + 1
    while True:
        base = 10 ** L + ct.K + sum(c * m * 10 ** ct.qmin for c, m in zip(coefs, mult))  # crude lower bound on X for this L
        if base > N: break
        R = N - ct.K - 10 ** L
        if R > 0:
            dfs(R, L, list(mult), [[] for _ in coefs], L)
        L += 1
    return sols

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
                    if cls_of_point(ct, L, grps, M) == cls: mine.append([L] + grps)
                mine.sort()
                if mine != sorted(x['sol']): ct.bad("leaf %s: sz solutions %s != declared %s" % (i, mine, x['sol']))
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
    for L in range(ct.qmin + 1, BRUTE + 1):
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
                brute.append([L] + groups)
                li = locate(L, groups)
                if li is None or 'sz' not in nodes[li].get('x', {}) or [L] + groups not in nodes[li]['x']['sol']:
                    ct.bad("brute smooth point %s not recorded in an sz leaf" % ([L] + groups))
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
