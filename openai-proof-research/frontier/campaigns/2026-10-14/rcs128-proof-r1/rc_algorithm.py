# Independent reviewer end-to-end executable model (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Independent executable model of the RCS128 candidate algorithm, written by the
reviewer from candidate.md and the pinned source sections 02-07 (not from author
code).  Every inequality the candidate asserts at a step is checked with an
assertion, and budgets are charged to disjoint accounts.  The final graph is
checked to be balanced, tau-invariant, parity-correct and connected to the empty
word; a half-Euler walk is extracted and the output word is checked.

This is a FINITE DIAGNOSTIC.  Passing runs are not a proof; an assertion failure
would be either an implementation error or a concrete counterexample to a step.
"""
import random
from collections import Counter, defaultdict
from rc_counts import counts, make_rho


class Fail(AssertionError):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


# ---------------------------------------------------------------- helpers
def least_period_circ(T):
    P = len(T)
    for p in range(1, P + 1):
        if P % p == 0 and T == T[:p] * (P // p):
            return p
    return P


def min_rot(s):
    return min(s[i:] + s[:i] for i in range(len(s)))


def max_rot_index(s):
    best = None
    for i in range(len(s)):
        r = s[i:] + s[:i]
        if best is None or r > best[0]:
            best = (r, i)
    return best[1]


class Layer:
    def __init__(self, lid, group, rank, z):
        self.id, self.group, self.rank, self.z = lid, group, rank, z
        self.p = group.p

    def Z(self, x):
        q, r = divmod(x, self.p)
        return self.z[r] + q * self.p

    def f(self, x):
        return self.Z(x - 1)

    def l(self, x):
        return self.Z(x)

    def visits(self, x, e):
        return self.Z(x - 1) <= e <= self.Z(x)

    def windows(self):
        for x in range(self.p):
            for e in range(self.Z(x - 1), self.Z(x) + 1):
                yield (x, e)

    def minlen(self):
        return min(self.Z(x - 1) - x for x in range(self.p))

    def minwin(self):
        x = min(range(self.p), key=lambda x: (self.Z(x - 1) - x, x))
        return (x, self.Z(x - 1))


class Group:
    def __init__(self, G):
        self.G, self.p = G, len(G)
        self.layers = []

    def ch(self, y):
        return self.G[y % self.p]

    def word(self, x, e):
        return ''.join(self.G[y % self.p] for y in range(x, e))


class ZPath:
    """A one-turn monotone staircase given by its exit function (used for spliced E,F)."""
    def __init__(self, p, zfun):
        self.p = p
        self.z = [zfun(x) for x in range(p)]

    Z = Layer.Z
    f = Layer.f
    l = Layer.l
    visits = Layer.visits


# ---------------------------------------------------------------- model
class Model:
    def __init__(self, words, cm, seed=0):
        self.words, self.cm, self.seed = list(words), cm, seed
        self.rho = make_rho(cm)
        c = counts(words, cm, 'broad')
        self.m, self.V, self.alpha, self.W = c['m'], c['V'], c['alpha'], c['W']
        self.R = c['R']
        self.added = []          # list of walks (each a list of edges); tau images added separately
        self.charges = defaultdict(int)
        self.account_budget = {}
        self.layer_account = {}
        self.log = Counter()

    # ---- edges
    def tau(self, ed):
        k, w = ed
        return ('D' if k == 'U' else 'U', self.rho(w))

    @staticmethod
    def ends(ed):
        k, w = ed
        return (w[:-1], w) if k == 'U' else (w, w[1:])

    def M(self, s):
        return self.m.get(s, 0)

    # ---- base graph and tau-paired transitions
    def base(self):
        edges, tau = [], {}
        for s in sorted(v for v in self.V if v):
            u = self.M(s) - sum(self.M(c + s) for c in self.alpha)
            d = self.M(s) - sum(self.M(s + c) for c in self.alpha)
            need(u >= 0 and d >= 0, 'negative multiplicity')
            need(u == self.M(self.rho(s)) - sum(self.M(self.rho(s) + c) for c in self.alpha), 'u(s)!=d(rho s)')
            for _ in range(u):
                a = len(edges)
                edges.append(('U', s))
                edges.append(('D', self.rho(s)))
                tau[a], tau[a + 1] = a + 1, a
        self.base_edges, self.base_tau = edges, tau
        need(sum(1 for e in edges if e[0] == 'U') == self.W, 'up count != W')
        out, inc = defaultdict(list), defaultdict(list)
        for i, ed in enumerate(edges):
            a, b = self.ends(ed)
            out[a].append(i)
            inc[b].append(i)
        verts = set(out) | set(inc)
        for v in verts:
            need(len(out[v]) == len(inc[v]), 'base not balanced')
            if v == self.rho(v):
                need(len(out[v]) % 2 == 0, 'odd fixed outdegree')
        rng = random.Random(self.seed)
        succ = {}
        done = set()
        for v in sorted(verts):
            if v in done:
                continue
            w = self.rho(v)
            done.update((v, w))
            if v == w:
                os = out[v][:]
                rng.shuffle(os)
                for a, b in zip(os[::2], os[1::2]):
                    succ[tau[a]] = b
                    succ[tau[b]] = a
            else:
                ins, os = inc[v][:], out[v][:]
                rng.shuffle(os)
                for a, b in zip(ins, os):
                    succ[a] = b
                    succ[tau[b]] = tau[a]
        need(len(succ) == len(edges) and len(set(succ.values())) == len(edges), 'transition not permutation')
        cycles, seen = [], set()
        for i in range(len(edges)):
            if i in seen:
                continue
            cyc, j = [], i
            while j not in seen:
                seen.add(j)
                cyc.append(j)
                j = succ[j]
            need(j == i, 'transition cycle broken')
            cycles.append(cyc)
        cid = {}
        for n, cyc in enumerate(cycles):
            for e in cyc:
                cid[e] = n
        for n, cyc in enumerate(cycles):
            partner = {cid[tau[e]] for e in cyc}
            need(len(partner) == 1 and n not in partner, 'cycle not paired with a distinct reversed cycle')
        self.cycles = cycles

    # ---- lifts, groups, sorted layers
    def layers(self):
        E = self.base_edges
        groups = {}
        exits = defaultdict(lambda: defaultdict(list))
        for cyc in self.cycles:
            seq = [E[i] for i in cyc]
            Tc = ''.join(w[-1] for k, w in seq if k == 'U')
            P = len(Tc)
            need(P > 0 and P == sum(1 for k, w in seq if k == 'D'), 'walk not balanced')
            s0 = self.ends(seq[0])[0]
            x, e = -len(s0), 0
            A = lambda y: Tc[y % P]
            need(''.join(A(y) for y in range(x, e)) == s0, 'lift does not spell start vertex')
            Zc = {}
            for k, w in seq:
                if k == 'U':
                    e += 1
                else:
                    Zc[x] = e
                    x += 1
                need(''.join(A(y) for y in range(x, e)) == (w if k == 'U' else w[1:]), 'lift mismatch')
            p = least_period_circ(Tc)
            prim = Tc[:p]
            G = min_rot(prim)
            r = next(i for i in range(p) if prim[i:] + prim[:i] == G)
            groups.setdefault(G, Group(G))
            for xc, zc in Zc.items():
                y, zz = xc - r, zc - r
                q, y0 = divmod(y, p)
                exits[G][y0].append(zz - q * p)
        self.groups = groups
        self.all_layers = []
        for G, g in sorted(groups.items()):
            p = g.p
            h = len(exits[G][0])
            need(all(len(exits[G][y]) == h for y in range(p)), 'unequal passage counts')
            srt = {y: sorted(exits[G][y], reverse=True) for y in range(p)}
            for rank in range(h):
                L = Layer(len(self.all_layers), g, rank, [srt[y][rank] for y in range(p)])
                for xx in range(-p, 2 * p):
                    need(L.Z(xx - 1) <= L.Z(xx) and L.Z(xx - 1) >= xx, 'layer property')
                g.layers.append(L)
                self.all_layers.append(L)
        need(sum(L.p for L in self.all_layers) == self.W, 'budgets do not sum to W')
        # orbits, reflection constants
        for G, g in groups.items():
            rG = min_rot(self.rho(G))
            need(rG in groups, 'partner group missing')
            g.partner = groups[rG]
            g.selfrev = (rG == G)
            pc = [c for c in range(g.p) if all(self.cm[g.G[y]] == g.partner.G[(c - 1 - y) % g.p] for y in range(g.p))]
            need(len(pc) == 1, 'reflection constant not unique')
            g.c = pc[0]
            g.t = max_rot_index(G)
            g.maxrot = G[g.t:] + G[:g.t]
        for G, g in groups.items():
            need(len(g.layers) == len(g.partner.layers), 'partner layer count')
            if g.selfrev:
                need(len(g.layers) % 2 == 0, 'odd number of self layers')
            for L in g.layers:
                RL = g.partner.layers[L.rank]
                refl = {self.rwin(g, x, e) for (x, e) in L.windows()}
                refl = {(x % g.p, e - (x - x % g.p)) for (x, e) in refl}
                need(refl == set(RL.windows()), 'reflection does not preserve sorted rank')
        # orbits
        self.orbits = []
        seenG = set()
        for G in sorted(groups, key=lambda G: (len(G), G)):
            if G in seenG:
                continue
            g = groups[G]
            seenG.update((G, g.partner.G))
            if g.selfrev:
                canon = g
            else:
                canon = g if g.maxrot > g.partner.maxrot else g.partner
            self.orbits.append(canon)
        for g in groups.values():
            g.canon = g if (g.selfrev or g.maxrot > g.partner.maxrot) else g.partner

    def rwin(self, g, x, e):
        """reflect window [x,e) of group g to partner coordinates"""
        return (g.c - e, g.c - x)

    # ---- pairs and accounts
    def pairs(self):
        self.pair_of = {}
        self.pairs_of_orbit = {}
        for A in self.orbits:
            P = []
            if A.selfrev:
                Ls = A.layers
                for i in range(0, len(Ls), 2):
                    P.append((Ls[i], Ls[i + 1]))
            else:
                for L in A.layers:
                    P.append((L, A.partner.layers[L.rank]))
            self.pairs_of_orbit[A.G] = P
            for idx, pr in enumerate(P):
                for L in pr:
                    self.pair_of[L.id] = (A.G, idx)
                self.account_budget[(A.G, idx)] = pr[0].p + pr[1].p
            if A.selfrev:
                for (D1, D2) in P:
                    U, Vv = self.axes(A, D1)
                    for (x, e) in (U, Vv):
                        need(D2.visits(x, e), 'lower pair member misses an axis vertex of upper member')
                    U2, V2 = self.axes(A, D2)
                    need({U, Vv} == {U2, V2}, 'pair axis sets differ')
                    self.log['self_pairs_both_axes'] += 1

    def axes(self, g, L):
        av = []
        for x in range(g.p):
            for e in range(L.Z(x - 1), L.Z(x) + 1):
                if (x + e - g.c) % g.p == 0:
                    av.append((x, e))
        need(len(av) == 2, 'not exactly two axis vertices per turn')
        av.sort(key=lambda v: v[0] + v[1])
        return av[0], av[1]

    # ---- walks
    def ow(self, text, wins):
        """source lem:ordered-windows; returns list of edges and up cost"""
        out = []
        for (a, b), (c, d) in zip(wins, wins[1:]):
            need(a <= c and b <= d, 'ordered windows violated: %r' % (wins,))
            for W_ in ((a, b), (c, d)):
                need(self.word(text, *W_) in self.V, 'prescribed window not in V')
            if c <= b:
                for s in range(a, c):
                    out.append(('D', self.word(text, s, b)))
                for e in range(b + 1, d + 1):
                    out.append(('U', self.word(text, c, e)))
            else:
                for s in range(a, b):
                    out.append(('D', self.word(text, s, b)))
                for j in range(b, c):
                    out.append(('U', self.word(text, j, j + 1)))
                    out.append(('D', self.word(text, j, j + 1)))
                for e in range(c + 1, d + 1):
                    out.append(('U', self.word(text, c, e)))
        for k, w in out:
            need(w in self.V and w, 'walk word outside V')
        return out

    @staticmethod
    def word(text, x, e):
        return text.word(x, e)

    def roundtrip(self, w):
        need(w in self.V, 'round trip word not in V')
        return [('U', w[:i]) for i in range(1, len(w) + 1)] + [('D', w[i:]) for i in range(len(w))]

    @staticmethod
    def cost(walk):
        return sum(1 for k, w in walk if k == 'U')

    def add(self, walk, account, tag, dry=False):
        """add walk and its tau image; charge both to account (dry: check only)"""
        bal = Counter()
        for ed in walk:
            a, b = self.ends(ed)
            bal[a] += 1
            bal[b] -= 1
        need(all(v == 0 for v in bal.values()), 'added walk not closed/balanced: ' + tag)
        if dry:
            self.log['shadow_' + tag] += 1
            return
        self.added.append(walk)
        self.charges[account] += 2 * self.cost(walk)
        self.log[tag] += 1

    # ---- record search (source sec05 record forcing)
    def find_record(self, A, t, H, K, minus_alignment_count):
        w = A.word(t, H - K)
        need(len(w) > 0, 'w empty')
        for L in self.all_layers:
            g = L.group
            for (x, e) in L.windows():
                for j in range(x, e - len(w) + 1):
                    if g.word(j, j + len(w)) != w:
                        continue
                    delta = t - j
                    if g.p == A.p and all(g.ch(y) == A.ch(y + delta) for y in range(g.p)):
                        continue
                    if all(g.ch(y) == A.ch(y + delta) for y in range(x, e)):
                        return dict(D=L, Dwin=(x, e), delta=delta, a=x + delta, b=e + delta)
        raise Fail('no different-alignment record found (count rule consequence)')

    # ---- main processing
    def run(self):
        self.base()
        self.layers()
        self.pairs()
        self.status = {}          # layer id -> 'rooted' | ('unit', uid)
        self.units = []
        self.incoming = defaultdict(list)   # recipient pair key -> list of batches
        for A in sorted(self.orbits, key=lambda g: (g.p, g.G)):
            self.process(A)
        self.cycles_phase()
        return self.finish()

    def mark(self, pair_key, how):
        A, idx = pair_key
        for L in self.pairs_of_orbit[A][idx]:
            self.status[L.id] = how

    def pair_layers(self, key):
        return self.pairs_of_orbit[key[0]][key[1]]

    # reflect a request (original -> mirror)
    def mirror_request(self, rq):
        hg, cg = rq['host'].group, rq['req'].group
        hx, he = rq['hwin']
        mh = hg.partner.layers[rq['host'].rank]
        mr = cg.partner.layers[rq['req'].rank]
        mwin = (hg.c - he, hg.c - hx)
        mdelta = cg.c - hg.c - rq['delta']
        a, e = rq['rwin']
        mrwin = (cg.c - e, cg.c - a)
        out = dict(host=mh, hwin=mwin, delta=mdelta, req=mr, rwin=mrwin, child=rq['child'])
        need(hg.partner.word(*mwin) == self.rho(hg.word(hx, he)), 'mirrored record word')
        need(cg.partner.word(*mrwin) == self.rho(cg.word(a, e)), 'mirrored requester word')
        need(mr.visits(*self.norm(mrwin, cg.p)), 'mirrored requester window not actual')
        need(all(hg.partner.ch(y) == cg.partner.ch(y + mdelta) for y in range(*mwin)), 'mirrored agreement')
        return out

    @staticmethod
    def norm(win, p):
        x, e = win
        q = (x // p) * p
        return (x - q, e - q)

    def process(self, A):
        p = A.p
        P = self.pairs_of_orbit[A.G]
        keys = [(A.G, i) for i in range(len(P))]
        recips = [k for k in keys if self.incoming.get(k)]
        anchor = {}
        for k in recips:
            anchor[k] = self.host(k)
            self.mark(k, 'rooted')
        base = min((k[1] for k in recips), default=None)
        # lower pairs
        if base is not None:
            S_layer_group, S = anchor[(A.G, base)]
            for idx in range(base + 1, len(P)):
                k = (A.G, idx)
                if k in recips:
                    continue
                Lu = P[idx][0] if A.selfrev else (P[idx][0] if P[idx][0].group is S_layer_group else P[idx][1])
                need(Lu.group is S_layer_group, 'lower link group mismatch')
                g = Lu.group
                if Lu.minlen() <= p:
                    walk = self.roundtrip(g.word(*Lu.minwin()))
                else:
                    a, h = S
                    need(h - a < 2 * p, 'baseline short vertex not < 2q')
                    e = min(Lu.l(a), h)
                    need(Lu.visits(a, e) and p < e - a <= h - a < 2 * p, 'lower link window')
                    walk = self.ow(g, [(a, h), (a + p, e + p), (a + p, h + p)])
                    need(self.cost(walk) == p, 'lower link cost')
                self.add(walk, k, 'lower_link')
                self.mark(k, 'rooted')
        upper = list(range(0, base if base is not None else len(P)))
        if not upper:
            return
        if A.selfrev:
            self.upper_self(A, upper, base)
        else:
            self.upper_nonself(A, upper, base)

    def upper_nonself(self, A, upper, base):
        p = A.p
        n = len(upper)
        Ls = [A.layers[i] for i in upper]
        acct = ('upper', A.G)
        self.account_budget[acct] = 0
        t = A.t
        top = Ls[0]
        H = top.f(t)
        baseL = A.layers[base] if base is not None else None
        if H - t <= n * p:
            self.add(self.roundtrip(A.word(t, H)), acct, 'easy_root')
            self.pool(acct, [(A.G, i) for i in upper])
            return
        if baseL is not None and baseL.l(t) >= H - n * p:
            E_ = baseL.l(t)
            if E_ < H:
                walk = self.ow(A, [(t, E_), (t, H), (t + n * p, E_ + n * p)])
                need(self.cost(walk) == n * p, 'band cost')
                self.add(walk, acct, 'easy_band')
            self.pool(acct, [(A.G, i) for i in upper])
            return
        k = 1
        while sum(1 for L in A.layers if L.l(t) >= H - k * p) > k:
            k += 1
        need(k <= n, 'threshold exceeded n')
        K = k * p
        rec = self.find_record(A, t, H, K, k)
        self.log['hard_nonself'] += 1
        a, b = rec['a'], rec['b']
        q = rec['D'].p
        need(a <= t and b >= H - K and b - a < p + q, 'record inequalities')
        if q == p:
            need(b - a < p, 'equal period record length')
        Lstar = Ls[k - 1]
        rH, rL = top.f(a), Lstar.l(a)
        need(rH - rL <= K and rH <= b + K, 'block preconditions')
        need(Lstar.l(t) >= H - (k - 1) * p, 'sharp band')
        in_block = set()
        if rL + K >= b:
            in_block = set(range(k))
            self.new_unit(A, [(A.G, upper[i]) for i in range(k)], 'collective',
                          dict(layers=Ls[:k], rec=rec, K=K, t=t, H=H, rH=rH, text=A))
        for i, L in enumerate(Ls):
            if i in in_block:
                continue
            key = (A.G, upper[i])
            need(L.f(a) <= b, 'individual: f(a)<=b')
            self.individual(A, L, key, rec, a, b, p, q)

    def individual(self, A, L, key, rec, a, b, p, q):
        if L.minlen() <= p:
            self.add(self.roundtrip(A.word(*L.minwin())), key, 'indiv_root')
            self.mark(key, 'rooted')
        elif L.l(a) + p >= b:
            self.new_unit(A, [key], 'individual', dict(layers=[L], rec=rec, text=A, K=p))
            self.log['individual_units'] += 1
        else:
            e = L.f(a)
            need(a + p < e <= L.l(a) < b - p, 'request inequality')
            need(q > p, 'request period not larger')
            D = rec['D']
            rq = dict(host=D, hwin=rec['Dwin'], delta=rec['delta'], req=L,
                      rwin=(a, e), child=A.G)
            need(all(D.group.ch(y) == A.ch(y + rec['delta']) for y in range(*rec['Dwin'])), 'record agreement')
            mq = self.mirror_request(rq)
            hk = self.pair_of[D.id]
            batch = self.incoming[hk]
            for bt in batch:
                if bt['child'] == A.G:
                    bt['items'].append((rq, mq, key))
                    break
            else:
                batch.append(dict(child=A.G, items=[(rq, mq, key)]))
            self.status[L.id] = 'requested'
            self.mark(key, 'requested')
            self.log['requests'] += 1

    def pool(self, acct, keys):
        self.account_budget[acct] = sum(self.account_budget.pop(k) for k in keys)
        for k in keys:
            self.mark(k, 'rooted')

    def new_unit(self, A, keys, kind, plan):
        uid = len(self.units)
        acct = ('unit', uid)
        self.account_budget[acct] = sum(self.account_budget.pop(k) for k in keys)
        u = dict(id=uid, orbit=A, keys=keys, kind=kind, plan=plan)
        self.units.append(u)
        for k in keys:
            self.mark(k, ('unit', uid))
        return u

    def upper_self(self, A, upper, base):
        p = A.p
        P = self.pairs_of_orbit[A.G]
        r = len(upper)
        Ls = [L for i in upper for L in P[i]]
        acct = ('upper', A.G)
        t = A.t
        top = Ls[0]
        H = top.f(t)
        baseL = P[base][0] if base is not None else None
        if H - t <= r * p:
            self.account_budget[acct] = 0
            self.add(self.roundtrip(A.word(t, H)), acct, 'easy_root_self')
            self.pool(acct, [(A.G, i) for i in upper])
            return
        if baseL is not None and baseL.l(t) >= H - r * p:
            self.account_budget[acct] = 0
            E_ = baseL.l(t)
            if E_ < H:
                walk = self.ow(A, [(t, E_), (t, H), (t + r * p, E_ + r * p)])
                self.add(walk, acct, 'easy_band_self')
            self.pool(acct, [(A.G, i) for i in upper])
            return
        k = 1
        while sum(1 for L in A.layers if L.l(t) >= H - k * p) > 2 * k:
            k += 1
        need(k <= r, 'self threshold exceeded r')
        K = k * p
        core = Ls[:2 * k - 1]
        Lstar = core[-1]
        need(Lstar.l(t) >= H - (k - 1) * p, 'odd core sharp band')
        for x in range(t - 2 * p, t + 2 * p):
            need(top.f(x) - Lstar.l(x) <= K, 'odd core wide band')
        rec = self.find_record(A, t, H, K, 2 * k)
        self.log['hard_self'] += 1
        a, b = rec['a'], rec['b']
        q = rec['D'].p
        need(a <= t and b >= H - K and b - a < p + q, 'record inequalities (self)')
        if q == p:
            need(b - a < p, 'equal period record (self)')
        rH, rL = top.f(a), Lstar.l(a)
        need(rH - rL <= K and rH <= b + K, 'odd core block preconditions')
        start = 0
        if rL + K >= b:
            self.new_unit(A, [(A.G, upper[i]) for i in range(k)], 'collective',
                          dict(layers=core, extra=Ls[2 * k - 1], rec=rec, K=K, t=t, H=H, rH=rH, text=A))
            self.log['odd_core_units'] += 1
            start = k
        else:
            self.log['odd_core_failed_tests'] += 1
        for i in range(start, r):
            key = (A.G, upper[i])
            Lu = P[upper[i]][0]
            need(Lu.f(a) <= b, 'self individual f(a)<=b')
            self.individual(A, Lu, key, rec, a, b, p, q)

    # ---- host requests with splice/flip/reclassify
    def host(self, key):
        A = self.groups[key[0]]
        q = A.p
        D1, D2 = self.pair_layers(key)
        batches = self.incoming[key]
        if A.selfrev:
            U, Vv = self.axes(A, D1)
            xu, xv = U[0], Vv[0]
            if xv < xu:
                xv += q

            def mk(Pa, Pb):
                def zf(x):
                    y = xu + ((x - xu) % q)
                    base_ = x - y
                    return (Pa.Z(y) if y < xv else Pb.Z(y)) + base_
                return ZPath(q, zf)
            Ep, Fp = mk(D1, D2), mk(D2, D1)
            for Pp in (Ep, Fp):
                for x in range(-q, 2 * q):
                    need(Pp.Z(x - 1) <= Pp.Z(x) and Pp.Z(x - 1) >= x, 'spliced path not a staircase')
            ewins = {(x, e) for x in range(q) for e in range(Ep.Z(x - 1), Ep.Z(x) + 1)}
            fwins = {(x, e) for x in range(q) for e in range(Fp.Z(x - 1), Fp.Z(x) + 1)}
            refl = {self.norm(self.rwin(A, x, e), q) for (x, e) in ewins}
            need(refl == fwins, 'tau(E) != F as window sets')
            need(Counter(self.pathedges(A, Ep)) + Counter(self.pathedges(A, Fp)) ==
                 Counter(self.pathedges(A, D1)) + Counter(self.pathedges(A, D2)), 'E+F != D1+D2')
            self.log['splices'] += 1
            onE = lambda rq: Ep.visits(*self.norm(rq['hwin'], q))
            first = batches[0]['items'][0][0]
            if not onE(first):
                Ep, Fp = Fp, Ep
                onE = lambda rq: Ep.visits(*self.norm(rq['hwin'], q))
            hostpath, hostgroup = Ep, A
        else:
            first = batches[0]['items'][0][0]
            Eh = first['host']
            hostpath, hostgroup = Eh, Eh.group
            onE = lambda rq: rq['host'] is Eh
        need(onE(first), 'anchor not on E')
        recs = []
        after = []
        anchored_ok = False
        for bi, bt in enumerate(batches):
            orig_on = onE(bt['items'][0][0])
            items = []
            for (rq, mq, rkey) in bt['items']:
                use = rq if orig_on else mq
                need(onE(use), 'batch record not on E after flip')
                cg = use['req'].group
                p_ = cg.p
                hx, he = use['hwin']
                ac, bc = hx + use['delta'], he + use['delta']
                Lr = use['req']
                if orig_on:
                    need(use['rwin'][0] == ac, 'original request not left anchored')
                    e = use['rwin'][1]
                    need(ac + p_ < e <= bc - p_, 'original request condition')
                    items.append((use, rkey, e - use['delta']))
                    if bi == 0:
                        anchored_ok = True
                    continue
                need(Lr.f(ac) <= bc, 'reflected requester f(a\') <= b\'')
                if Lr.minlen() <= p_:
                    self.add(self.roundtrip(cg.word(*Lr.minwin())), rkey, 'reclass_case1')
                    self.log['reclass1'] += 1
                elif Lr.l(ac) + p_ >= bc:
                    ep = max(bc, Lr.f(ac + p_))
                    need(Lr.visits(ac + p_, ep) and bc <= ep <= bc + p_, 'case2 window')
                    after.append((cg, [(ac, bc), (ac + p_, ep), (ac + p_, bc + p_)], rkey, p_))
                    self.log['reclass2'] += 1
                else:
                    e = Lr.f(ac)
                    need(ac + p_ < e <= Lr.l(ac) < bc - p_, 'reclassified case3 condition')
                    items.append((use, rkey, e - use['delta']))
                    self.log['reclass3'] += 1
            if items:
                recs.append(dict(child=bt['child'], hwin=items[0][0]['hwin'], delta=items[0][0]['delta'],
                                 cg=items[0][0]['req'].group, reqs=[(it[0]['req'], it[1], it[2]) for it in items]))
                need(all(it[0]['hwin'] == items[0][0]['hwin'] for it in items), 'batch uses several records')
        need(anchored_ok and recs, 'no surviving anchored case3 request')
        self.host_lemma(hostgroup, hostpath, recs, key)
        self.shadow_reclassify(batches, key, A)
        for (cg, wins, rkey, p_) in after:
            walk = self.ow(cg, wins)
            need(self.cost(walk) == p_, 'case2 link cost')
            self.add(walk, rkey, 'case2_after_host')
        for bt in batches:
            for (rq, mq, rkey) in bt['items']:
                self.mark(rkey, 'rooted')
        # anchor short record for baseline/lower links: the first record on E
        hx, he = recs[0]['hwin']
        need(he - hx < 2 * q, 'anchor record not < 2q')
        return hostgroup, (hx, he)

    def shadow_reclassify(self, batches, key, A):
        """Dry-run check of the reflected-batch reclassification lemma for EVERY
        request: reflect each original request onto the mirrored record, reapply
        the three individual cases, check the claimed inequalities, build (but do
        not add) case-2 links, and dry-run the source host lemma on the mirrored
        host path with the reclassified case-3 requests."""
        recs = []
        hostpath = hostgroup = None
        for bt in batches:
            items = []
            for (rq, mq, rkey) in bt['items']:
                cg = mq['req'].group
                p_ = cg.p
                hx, he = mq['hwin']
                ac, bc = hx + mq['delta'], he + mq['delta']
                Lr = mq['req']
                ra, re_ = mq['rwin']
                need(re_ == bc and ac + p_ <= ra, 'reflected requester is not right anchored inside R\'')
                need(Lr.f(ac) <= bc, 'shadow: reflected requester f(a\') <= b\'')
                self.log['shadow_reclass_checked'] += 1
                if Lr.minlen() <= p_:
                    self.log['shadow_reclass1'] += 1
                elif Lr.l(ac) + p_ >= bc:
                    ep = max(bc, Lr.f(ac + p_))
                    need(Lr.visits(ac + p_, ep) and bc <= ep <= bc + p_, 'shadow case2 window')
                    walk = self.ow(cg, [(ac, bc), (ac + p_, ep), (ac + p_, bc + p_)])
                    need(self.cost(walk) == p_, 'shadow case2 cost')
                    self.add(walk, rkey, 'case2_after_host', dry=True)
                else:
                    e = Lr.f(ac)
                    need(ac + p_ < e <= Lr.l(ac) < bc - p_, 'shadow reclassified case3 condition')
                    items.append((mq, rkey, e - mq['delta']))
                    self.log['shadow_reclass3'] += 1
            if items:
                h = items[0][0]['host']
                if A.selfrev:
                    D1, D2 = self.pair_layers(key)
                    U, Vv = self.axes(A, D1)
                    q = A.p
                    xu, xv = U[0], Vv[0]

                    def mk(Pa, Pb):
                        def zf(x):
                            y = xu + ((x - xu) % q)
                            return (Pa.Z(y) if y < xv else Pb.Z(y)) + (x - y)
                        return ZPath(q, zf)
                    cands = [mk(D1, D2), mk(D2, D1)]
                    hp = next((P for P in cands if P.visits(*self.norm(items[0][0]['hwin'], q))), None)
                    need(hp is not None, 'shadow record on neither spliced path')
                    hostpath, hostgroup = hp, A
                else:
                    if hostpath is None:
                        hostpath, hostgroup = h, h.group
                    if h is not hostpath:
                        continue
                if not all(hostpath.visits(*self.norm(it[0]['hwin'], hostgroup.p)) for it in items):
                    continue
                recs.append(dict(child=bt['child'], hwin=items[0][0]['hwin'], delta=items[0][0]['delta'],
                                 cg=items[0][0]['req'].group, reqs=[(it[0]['req'], it[1], it[2]) for it in items]))
        if recs:
            if A.selfrev:
                recs = [r for r in recs if hostpath.visits(*self.norm(r['hwin'], A.p))]
            if recs:
                self.host_lemma(hostgroup, hostpath, recs, key, dry=True)

    def pathedges(self, g, P):
        out = []
        for x in range(g.p):
            for e in range(P.Z(x - 1) + 1, P.Z(x) + 1):
                out.append(('U', g.word(x, e)))
            out.append(('D', g.word(x, P.Z(x))))
        return out

    def host_lemma(self, hg, hp, recs, hkey, dry=False):
        q = hg.p
        for R in recs:
            a, b = R['hwin']
            need(hp.visits(*self.norm((a, b), q)), 'record not on host path')
            need(all(hg.ch(y) == R['cg'].ch(y + R['delta']) for y in range(a, b)), 'record agreement')
            need(b - a < R['cg'].p + q, 'host-length bound')
        j = min(range(len(recs)), key=lambda i: (recs[i]['cg'].p, i))
        Rj = recs[j]
        aj, bj = Rj['hwin']
        sj = aj + bj
        others = []
        for i, R in enumerate(recs):
            if i == j:
                continue
            a, b = R['hwin']
            kk = 0
            while a + b + 2 * kk * q < sj:
                kk += 1
            while a + b + 2 * kk * q >= sj + 2 * q:
                kk -= 1
            sh = kk * q
            others.append(dict(R, hwin=(a + sh, b + sh), delta=R['delta'] - sh,
                               reqs=[(L, rk, e + sh) for (L, rk, e) in R['reqs']]))
        others.sort(key=lambda R: (R['hwin'][0] + R['hwin'][1], R['hwin']))
        T = aj + q
        for R in others:
            a, b = R['hwin']
            need(aj <= a <= T and bj <= b <= bj + q, 'host order')
        jreqs = sorted(Rj['reqs'], key=lambda t: t[2])
        wins = [(aj, e) for (_, _, e) in jreqs] + [(aj, bj)]
        loops = []
        for R in others:
            a, b = R['hwin']
            pi = R['cg'].p
            for (L, rk, e) in sorted(R['reqs'], key=lambda t: t[2]):
                Q = (min(a + pi, T), max(e, bj))
                need(a <= Q[0] < Q[1] <= b, 'target not inside record')
                wins.append(Q)
                d = R['delta']
                cw = [(Q[0] + d, Q[1] + d), (a + pi + d, e + pi + d), (Q[0] + d + pi, Q[1] + d + pi)]
                need(L.visits(*self.norm((a + d, e + d), pi)), 'requester window not actual')
                need(hg.word(*Q) == R['cg'].word(*cw[0]), 'target word disagreement')
                loops.append((R['cg'], cw, rk, pi))
        e0 = jreqs[0][2]
        wins.append((T, e0 + q))
        walk = self.ow(hg, wins)
        need(self.cost(walk) == q, 'host excursion cost != q')
        self.add(walk, hkey, 'host_excursion', dry)
        for (cg, cw, rk, pi) in loops:
            lw = self.ow(cg, cw)
            need(self.cost(lw) == pi, 'requester loop cost')
            self.add(lw, rk, 'host_child_loop', dry)
        hl = wins[-2][1]
        pj = Rj['cg'].p
        if hl > T:
            need(hl - T < pj, 'host short contact too long')
            self.add(self.roundtrip(hg.word(T, hl)), jreqs[0][1], 'host_contact_root', dry)
        self.log['host_applications' if not dry else 'shadow_host_applications'] += 1

    # ---- units: link realization, internal joins, cycles
    def unit_target(self, u):
        D = u['plan']['rec']['D']
        st = self.status.get(D.id)
        if st == 'rooted':
            return None
        need(isinstance(st, tuple) and st[0] == 'unit', 'target neither rooted nor in a unit: %r' % (st,))
        return st[1]

    def link_walk(self, u, contact_q=None):
        pl = u['plan']
        A, rec = pl['text'], pl['rec']
        a, b = rec['a'], rec['b']
        if u['kind'] == 'individual':
            L = pl['layers'][0]
            p = A.p
            ep = max(b, L.f(a + p))
            need(L.visits(a + p, ep) and b <= ep <= b + p, 'individual link window')
            walk = self.ow(A, [(a, b), (a + p, ep), (a + p, b + p)])
            need(self.cost(walk) == p, 'individual cost')
            return walk, None
        K = pl['K']
        Ls = pl['layers']
        if contact_q is not None and all(L.minlen() > contact_q for L in Ls):
            t, H = pl['t'], pl['H']
            need(b - t < contact_q, 'max-rotation consequence b-t<q failed')
            x = min(t, a + K)
            F = Ls[0].f(x)
            need(b - x < contact_q and b < F <= H <= b + K, 'cycle contact inequalities')
            for L in Ls:
                need(b < L.f(x) <= F, 'constituent first end at x')
            walk = self.ow(A, [(a, b), (x, b), (x, F), (a + K, b + K)])
            need(self.cost(walk) == K, 'cycle contact cost')
            return walk, A.word(x, b)
        rH = pl['rH']
        Y = max(b, rH)
        wins = [(a, b)]
        for L in Ls:
            xi = a
            while L.Z(xi) < Y:
                xi += 1
            need(xi <= a + K and L.visits(xi, Y), 'collective height not met')
            wins.append((xi, Y))
        wins.append((a + K, b + K))
        walk = self.ow(A, wins)
        need(self.cost(walk) == K, 'collective cost')
        return walk, None

    def internal_join(self, u):
        if u['kind'] == 'individual':
            return
        pl = u['plan']
        A, t, H, K = pl['text'], pl['t'], pl['H'], pl['K']
        p = A.p
        h = K - p
        E_ = pl['layers'][-1].l(t)
        need(H - E_ <= h, 'internal band too wide')
        if E_ < H:
            walk = self.ow(A, [(t, E_), (t, H), (t + h, E_ + h)])
            need(self.cost(walk) == h, 'internal join cost')
            self.add(walk, ('unit', u['id']), 'internal_join')

    def canon_text(self, u):
        return u['orbit'].maxrot

    @staticmethod
    def cmp_periodic(s1, s2):
        n = len(s1) + len(s2)
        a = (s1 * (n // len(s1) + 1))[:n]
        b = (s2 * (n // len(s2) + 1))[:n]
        return (a > b) - (a < b)

    def cycles_phase(self):
        tgt = {u['id']: self.unit_target(u) for u in self.units}
        state = {}
        handled = set()
        for u in self.units:
            if u['id'] in state:
                continue
            path, pos = [], {}
            cur = u['id']
            while cur is not None and cur not in state and cur not in pos:
                pos[cur] = len(path)
                path.append(cur)
                cur = tgt[cur]
            if cur is not None and cur in pos:
                cyc = path[pos[cur]:]
                self.open_cycle(cyc, tgt)
                handled.update(cyc)
            for x in path:
                state[x] = 1
        for u in self.units:
            if u['id'] in handled:
                continue
            walk, _ = self.link_walk(u)
            self.add(walk, ('unit', u['id']), 'link')

    def open_cycle(self, cyc, tgt):
        if len(cyc) == 1:
            u = self.units[cyc[0]]
            self.internal_join(u)
            rec = u['plan']['rec']
            p = u['plan']['text'].p
            need(rec['b'] - rec['a'] < p, 'selfloop record not < p')
            self.add(self.roundtrip(u['plan']['text'].word(rec['a'], rec['b'])), ('unit', u['id']), 'selfloop_root')
            self.log['quotient_selfloops'] += 1
            return
        sel = cyc[0]
        for c in cyc[1:]:
            if self.cmp_periodic(self.canon_text(self.units[c]), self.canon_text(self.units[sel])) > 0:
                sel = c
        su = self.units[sel]
        T = self.units[tgt[sel]]
        q = T['plan']['text'].p
        walk, contact = self.link_walk(su, contact_q=q)
        if contact is None:
            if su['kind'] == 'individual':
                verts = [v for ed in walk for v in self.ends(ed)]
                contact = min(verts, key=len)
            else:
                Ls = su['plan']['layers']
                L = min(Ls, key=lambda L: L.minlen())
                contact = su['plan']['text'].word(*L.minwin())
        need(len(contact) <= q, 'selected contact longer than q')
        self.add(walk, ('unit', sel), 'cycle_selected_link')
        self.internal_join(T)
        if contact:
            self.add(self.roundtrip(contact), ('unit', T['id']), 'cycle_contact_root')
        for c in cyc:
            if c in (sel, T['id']):
                continue
            w2, _ = self.link_walk(self.units[c])
            self.add(w2, ('unit', c), 'link')
        self.log['quotient_cycles'] += 1
        self.log['max_cycle_len'] = max(self.log['max_cycle_len'], len(cyc))

    # ---- final graph, half-Euler, output
    def finish(self):
        for acct, spent in self.charges.items():
            need(acct in self.account_budget, 'charge to unknown/closed account %r' % (acct,))
            need(spent <= self.account_budget[acct], 'account over budget %r: %d > %d' % (acct, spent, self.account_budget[acct]))
        for L in self.all_layers:
            need(self.status.get(L.id) is not None, 'layer without status')
        edges = list(self.base_edges)
        tau = dict(self.base_tau)
        for walk in self.added:
            for ed in walk:
                i = len(edges)
                edges.append(ed)
                edges.append(self.tau(ed))
                tau[i], tau[i + 1] = i + 1, i
        U = sum(1 for e in edges if e[0] == 'U')
        need(U <= 2 * self.W, 'final up cost > 2W')
        out, inc = defaultdict(list), defaultdict(list)
        parent = {}

        def find(v):
            while parent.setdefault(v, v) != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        for i, ed in enumerate(edges):
            a, b = self.ends(ed)
            out[a].append(i)
            inc[b].append(i)
            parent[find(a)] = find(b)
        verts = set(out) | set(inc)
        for v in verts:
            need(len(out[v]) == len(inc[v]), 'final graph not balanced')
            if v == self.rho(v):
                need(len(out[v]) % 2 == 0, 'final fixed outdegree odd')
        need('' in verts, 'empty word not used')
        need(all(find(v) == find('') for v in verts), 'final graph not connected to empty')
        walk = self.half_euler(edges, tau, out)
        T = ''.join(edges[i][1][-1] for i in walk if edges[i][0] == 'U')
        need(len(T) == U // 2, 'half-Euler length')
        need(len(T) <= self.W, 'output longer than W')
        for s in self.words:
            need((not s) or s in T or self.rho(s) in T, 'output misses a requirement')
        return T, U

    def half_euler(self, edges, tau, out):
        rho = self.rho
        orb_edges = []
        seen = set()
        for i in range(len(edges)):
            if i in seen:
                continue
            seen.update((i, tau[i]))
            orb_edges.append(i)
        key = lambda v: min(v, rho(v))
        inc_at = defaultdict(list)   # vertex orbit -> list of (edge-orbit idx, end 0/1, sign)
        for n, i in enumerate(orb_edges):
            a, b = self.ends(edges[i])
            for endi, v in ((0, a), (1, b)):
                O = key(v)
                if O == rho(O):
                    sign = 0
                else:
                    rep = O
                    if v == rep:
                        sign = +1 if endi == 0 else -1
                    else:
                        sign = -1 if endi == 0 else +1
                inc_at[O].append((n, endi, sign))
        pair = {}
        for O, lst in inc_at.items():
            if O == rho(O):
                need(len(lst) % 2 == 0, 'odd quotient degree at fixed vertex')
                for x, y in zip(lst[::2], lst[1::2]):
                    pair[x[:2]] = y[:2]
                    pair[y[:2]] = x[:2]
            else:
                ps = [x for x in lst if x[2] > 0]
                ms = [x for x in lst if x[2] < 0]
                need(len(ps) == len(ms), 'signed incidence imbalance')
                for x, y in zip(ps, ms):
                    pair[x[:2]] = y[:2]
                    pair[y[:2]] = x[:2]
        vorb = {}
        for O, lst in inc_at.items():
            for x in lst:
                vorb[x[:2]] = O

        def trails():
            lab = {}
            n_ = 0
            for start in pair:
                if start in lab:
                    continue
                cur = start
                while cur not in lab:
                    lab[cur] = n_
                    other = (cur[0], 1 - cur[1])
                    lab[other] = n_
                    cur = pair[other]
                n_ += 1
            return lab, n_
        while True:
            lab, n_ = trails()
            if n_ == 1:
                break
            merged = False
            for O, lst in inc_at.items():
                incs = [x[:2] for x in lst]
                tr = {lab[x] for x in incs}
                if len(tr) < 2:
                    continue
                fixed = (O == rho(O))
                sgn = {x[:2]: x[2] for x in lst}
                x1 = incs[0]
                y1 = pair[x1]
                for x2 in incs:
                    if lab[x2] == lab[x1]:
                        continue
                    y2 = pair[x2]
                    if not fixed:
                        if sgn[x1] != sgn[x2]:
                            x2, y2 = y2, x2
                    pair[x1], pair[y2] = y2, x1
                    pair[x2], pair[y1] = y1, x2
                    merged = True
                    break
                if merged:
                    break
            need(merged, 'quotient not connected')
        # lift from the empty word
        start = next(x[:2] for x in inc_at[''])
        cur_v = ''
        walk = []
        inc_ = start
        used = set()
        for _ in range(len(orb_edges)):
            n, endi = inc_
            need(n not in used, 'edge orbit reused')
            used.add(n)
            i = orb_edges[n]
            a, b = self.ends(edges[i])
            if a == cur_v:
                walk.append(i)
                nxt = b
            else:
                j = tau[i]
                a2, b2 = self.ends(edges[j])
                need(a2 == cur_v, 'lift incompatible with state')
                walk.append(j)
                nxt = b2
            cur_v = nxt
            arrive = (n, 1 - endi)
            inc_ = pair[arrive]
        need(cur_v == '' and len(used) == len(orb_edges), 'half-Euler lift not closed')
        return walk


def solve(words, cm, seed=0):
    M = Model(words, cm, seed)
    if not M.R:
        return '', M
    T, U = M.run()
    return T, M
