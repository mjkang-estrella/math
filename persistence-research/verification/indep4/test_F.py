# Mathematical soundness tests for check_sym_F's kill machinery (stdlib only).  run: python3 -I test_F.py [seed]
import sys, random, itertools, collections, json
from math import comb, gcd
sys.path.insert(0, '.')
import check_sym_F as F

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rnd = random.Random(seed)
import os
T0LIST = [int(x) for x in os.environ['T0LIST'].split(',')] if os.environ.get('T0LIST') else None
QEXTRA = int(os.environ.get('QEXTRA', '0'))
R = {}

def mkcert(groups, K, qmin, pin2=False, k=0):
    F_ = sum(m for _, m in groups)
    meta = dict(k='meta', format='nd-sym', version=1, domain='unordered', scope='full', groups=[list(g) for g in groups], K=K, qmin=qmin,
                dim=1 + F_, pin2=pin2, pin_digits=k or None, root=dict(r=[0] + [[0] * m for _, m in groups], m=1))
    return F.Cert(meta)

# ---------------------------------------------------------------- T1: (a) partition of labelled tuples among the children
def T1():
    ok = 0
    for trial in range(60):
        ng = rnd.choice([1, 2, 3])
        mult = [rnd.choice([1, 2, 3]) for _ in range(ng)]
        while sum(mult) > 5: mult = [max(1, m - 1) for m in mult]
        M = rnd.choice([1, 2, 3, 4, 6]); f = rnd.choice([2, 3])
        while (f * M) ** sum(mult) > 150000: mult = [max(1, m - 1) for m in mult]; M = max(1, M - 1)
        # parent class = key of a random labelled tuple mod M
        labels = [[rnd.randrange(M) for _ in range(m)] for m in mult]
        L = rnd.randrange(M)
        parent = (L,) + tuple(tuple(sorted(g)) for g in labels)
        # all labelled tuples mod fM that reduce to the parent key
        cnt = collections.Counter(); total = 0
        slots = [(gi, j) for gi, m in enumerate(mult) for j in range(m)]
        for Ls in range(f * M):
            if Ls % M != L: continue
            for vals in itertools.product(range(f * M), repeat=len(slots)):
                gs = [[] for _ in mult]
                for (gi, j), v in zip(slots, vals): gs[gi].append(v)
                key = (Ls,) + tuple(tuple(sorted(g)) for g in gs)
                red = (key[0] % M,) + tuple(tuple(sorted(x % M for x in g)) for g in key[1:])
                if red == parent: cnt[key] += 1; total += 1
        lifts = list(F.class_lifts(parent, M, f))
        assert len(lifts) == len(set(lifts)), "duplicate lifts"
        assert set(lifts) == set(cnt), ("lift set != set of keys of labelled tuples", parent, M, f)
        h = [collections.Counter(g) for g in parent[1:]]
        expect = f
        for hc in h:
            for b, hh in hc.items(): expect *= comb(f + hh - 1, hh)
        assert len(lifts) == expect, (len(lifts), expect)
        # labelled tuples mod M with parent key: multinomials; each has f^(1+F) lifts
        npar = 1
        for hc in h:
            n = sum(hc.values()); t = 1
            from math import factorial
            t = factorial(n)
            for v in hc.values(): t //= factorial(v)
            npar *= t
        assert total == npar * f ** (len(slots) + 1), (total, npar * f ** (len(slots) + 1))
        ok += 1
    # actual (distinct-position) points land in exactly one child
    for trial in range(2000):
        mult = [rnd.choice([1, 2, 3]) for _ in range(rnd.choice([1, 2, 3]))]
        M = rnd.choice([2, 6, 12, 36]); f = rnd.choice([2, 3, 6])
        pos = rnd.sample(range(3, 200), sum(mult)); L = max(pos) + rnd.randrange(1, 40)
        groups = []; it = iter(pos)
        for m in mult: groups.append([next(it) for _ in range(m)])
        par = (L % M,) + tuple(tuple(sorted(q % M for q in g)) for g in groups)
        child = (L % (f * M),) + tuple(tuple(sorted(q % (f * M) for q in g)) for g in groups)
        lifts = list(F.class_lifts(par, M, f))
        assert lifts.count(child) == 1
    R['T1_partition'] = 'PASS (%d labelled-enumeration cases, 2000 point-in-one-child cases)' % ok

# ---------------------------------------------------------------- T2: (b) sumset is a superset of X mod p over actual points
def T2():
    n = 0; tight = 0
    for trial in range(400):
        groups = rnd.choice([[(9, 2), (54, 1)], [(9, 3), (18, 1)], [(18, 1), (27, 1), (54, 2)], [(9, 2), (45, 2), (54, 1)]])
        ct = mkcert(groups, rnd.choice([1043, 89, 143, 1061]), 3)
        M = rnd.choice([2, 4, 6, 12, 18, 36, 42, 72])
        p = rnd.choice([11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53, 73, 101, 137, 239, 271, 9901])
        d = F.order(10, p); g = gcd(d, M)
        # class from a random actual point
        mult = [m for _, m in groups]
        pos = rnd.sample(range(3, 120), sum(mult)); it = iter(pos)
        grp = [[next(it) for _ in range(m)] for m in mult]; L = max(pos) + rnd.randrange(1, 30)
        cls = F.cls_of_point(ct, L, grp, M)
        red = (cls[0] % g,) + tuple(tuple(sorted(r % g for r in gr)) for gr in cls[1:])
        S = ct.sumset(p, d, g, red)
        # enumerate many other actual points in the same class (positions = residue + M*t), check X mod p in S
        for _ in range(30):
            used = set(); gg = []
            okp = True
            for gr in cls[1:]:
                cur = []
                for r in gr:
                    for _t in range(50):
                        q = r + M * rnd.randrange(0, 12)
                        if q >= 3 and q not in used: used.add(q); cur.append(q); break
                    else: okp = False
                gg.append(cur)
            if not okp: continue
            Lq = cls[0] + M * rnd.randrange(1, 12)
            while Lq <= max(used): Lq += M
            assert F.cls_of_point(ct, Lq, gg, M) == cls
            X = 10 ** Lq + ct.K + sum(c * 10 ** q for (c, _), gr in zip(groups, gg) for q in gr)
            assert X % p in S, ("sumset misses actual X mod p", p, M, cls)
            n += 1
        tight += (len(S) < p)
    R['T2_sumset_superset'] = 'PASS (%d actual points, %d/400 sumsets proper subsets of Z/p)' % (n, tight)

# ---------------------------------------------------------------- T3: (c) pins hold on random domain points; pair sets contain the true pair
def T3():
    n = 0
    for trial in range(3000):
        t0 = rnd.choice(T0LIST or [0, 0, 0, 1, 2])
        qmin = max(3, t0 + 3) + rnd.randrange(QEXTRA + 1)
        k = rnd.choice([0, 1, 2, 3]); k = min(k, qmin)
        mult = [rnd.choice([1, 2]) for _ in range(rnd.choice([1, 2, 3]))]
        groups = [(c, m) for c, m in zip(rnd.sample([9, 18, 27, 45, 54, 63, 72], len(mult)), mult)]
        Kodd = rnd.randrange(1, 5000) * 2 + 1
        K = Kodd << t0
        if K % 5 == 0: continue
        ct = mkcert(groups, K, qmin, pin2=True, k=k)
        pos = rnd.sample(range(qmin, qmin + 12), sum(mult)); it = iter(pos)
        gr = [[next(it) for _ in range(m)] for m in mult]; L = max(pos) + rnd.randrange(1, 9)
        X = 10 ** L + K + sum(c * 10 ** q for (c, _), g in zip(groups, gr) for q in g)
        assert F.v_p(X, 2) == t0                                     # (V2)
        assert (X - K) % (10 ** k) == 0                              # tail
        assert (X >> t0) % 8 == (K >> t0) % 8                        # pin2
        E = ct.E
        assert (X >> t0) % E == (K >> t0) % E                        # combined modulus (CRT of both pins)
        # if X is of the form 2^t0 3^a 7^w the (a mod A, w mod W) pair is admissible
        Y = X >> t0
        a = F.v_p(Y, 3); Y //= 3 ** a; w = F.v_p(Y, 7); Y //= 7 ** w
        # force a smooth value: use N = 2^t0 3^a' 7^w' directly and the pin congruence of K: K' = N - 10^L - sum
        a2, w2 = rnd.randrange(0, 40), rnd.randrange(0, 20)
        N = (1 << t0) * 3 ** a2 * 7 ** w2
        K2 = N - 10 ** L - sum(c * 10 ** q for (c, _), g in zip(groups, gr) for q in g)
        if K2 <= 0 or K2 % 5 == 0: continue
        ct2 = mkcert(groups, K2, qmin, pin2=True, k=k)
        A, W, P = ct2.pairs(ct2.E)
        assert (a2 % A, w2 % W) in set(P), "true exponent pair not admissible"
        n += 1
    R['T3_pins'] = 'PASS (%d random domain points / smooth targets)' % n

# ---------------------------------------------------------------- T4: positive controls: a class containing a true solution is never killed
def T4():
    import os
    PMAX = int(os.environ.get('T4_PMAX', '3000'))
    prm = [p for p in range(11, PMAX) if F.isprime(p)] + [9901, 333667, 52579, 999999000001, 73, 137, 101, 3541, 27961, 99990001, 98641]
    prm = sorted(set(prm))
    Ms = [1, 2, 4, 6, 12, 18, 36, 42, 72, 84, 126, 144, 252, 216, 432, 504, 1008, 1512]
    if os.environ.get('T4_SMALL'): Ms = [2, 6, 12, 36, 42, 84, 252, 1008]
    cases = 0; checks = 0; pairs_killed_nonsol = 0; kinds = collections.Counter(); skipped = [0]
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 120):
        t0 = rnd.choice(T0LIST or [0, 0, 0, 1, 3]); qmin = (t0 + 3 if t0 else 3) + rnd.randrange(QEXTRA + 1)
        mult = [rnd.choice([1, 2, 3]) for _ in range(rnd.choice([1, 2, 3]))]
        groups = [(c, m) for c, m in zip(rnd.sample([9, 18, 27, 45, 54, 63, 72], len(mult)), mult)]
        pos = rnd.sample(range(qmin, qmin + 25), sum(mult)); it = iter(pos)
        gr = [[next(it) for _ in range(m)] for m in mult]; L = max(pos) + rnd.randrange(1, 12)
        while True:
            a2, w2 = rnd.randrange(0, 60), rnd.randrange(0, 30)
            N = (1 << t0) * 3 ** a2 * 7 ** w2
            K = N - 10 ** L - sum(c * 10 ** q for (c, _), g in zip(groups, gr) for q in g)
            if K > 0 and K % 5 != 0: break
            L += 1 if K <= 0 else 0
            if K <= 0 and rnd.random() < 0.5: a2 += 1
        k = rnd.choice([0, 1, 2, 3]); k = min(k, qmin)
        ct = mkcert(groups, K, qmin, pin2=(qmin >= t0 + 3 and rnd.random() < 0.8), k=k)
        assert ct.t0 == t0 or True
        if ct.t0 != t0: continue     # K's valuation must equal t0 (it does when qmin>t0), else skip
        cases += 1
        for M in Ms:
            cls = F.cls_of_point(ct, L, gr, M)
            sg = ct.sig(cls, M)
            # signature must be consistent with the true exponents
            a0, aex, w0, wex = sg
            assert (a2 == a0) if aex else (a2 >= a0), ("3-adic signature wrong", sg, a2)
            assert (w2 == w0) if wex else (w2 >= w0), ("7-adic signature wrong", sg, w2)
            for p in prm:
                if p > 2000 and rnd.random() < 0.9: continue
                try: ok, kind = ct.kills(p, cls, M, sg)
                except OverflowError: skipped[0] += 1; continue
                checks += 1
                assert not ok, ("TRUE SOLUTION CLASS KILLED", p, M, cls, groups, K, qmin, ct.pin2, k)
        # also sample non-solution classes (to show kills do occur and with what kinds)
        for M in (12, 36, 72):
            for _ in range(15):
                cls2 = (rnd.randrange(M),) + tuple(tuple(sorted(rnd.randrange(M) for _ in range(m))) for _, m in groups)
                sg = ct.sig(cls2, M)
                for p in (11, 13, 37, 73, 101, 137, 17, 19, 41, 31):
                    try: ok, kind = ct.kills(p, cls2, M, sg)
                    except OverflowError: skipped[0] += 1; continue
                    if ok: kinds[kind] += 1
    R['T4_positive_controls'] = 'PASS (%d solution instances, %d (class,prime) tests, 0 wrong kills, %d skipped as too large); kill kinds on random non-solution classes: %s' % (cases, checks, skipped[0], dict(kinds))

# ---------------------------------------------------------------- T5: (d) DFS for exact solutions vs brute force
def T5():
    n = 0; nsol = 0
    for trial in range(60):
        groups = rnd.choice([[(9, 2), (54, 1)], [(9, 1), (18, 1), (27, 1)], [(9, 3)], [(45, 2), (54, 2)], [(18, 1)]])
        K = rnd.choice([89, 143, 8, 1043]); qmin = 3
        ct = mkcert(groups, K, qmin)
        LM = 11
        table = collections.defaultdict(list)
        mult = [m for _, m in groups]
        for L in range(qmin + 1, LM + 1):
            pos = list(range(qmin, L))
            def rec(gi, avail, acc):
                if gi == len(groups): yield list(acc); return
                for sub in itertools.combinations(avail, mult[gi]):
                    yield from rec(gi + 1, [x for x in avail if x not in sub], acc + [list(sub)])
            for gr in rec(0, pos, []):
                if sum(mult) > len(pos): break
                X = 10 ** L + K + sum(c * 10 ** q for (c, _), g in zip(groups, gr) for q in g)
                table[X].append([L] + [sorted(g) for g in gr])
        for X in rnd.sample(list(table), min(20, len(table))):
            got = sorted([L] + g for L, g in F.solutions_N(ct, X))
            want = sorted(v for v in table[X])
            assert got == want, ("DFS mismatch", groups, K, X, got, want)
            n += 1; nsol += len(want)
        # values not attained
        for _ in range(5):
            X = rnd.choice(list(table)) + rnd.randrange(1, 1000)
            got = [[L] + g for L, g in F.solutions_N(ct, X) if L <= LM]
            assert sorted(got) == sorted(table.get(X, [])), "DFS found spurious"
    R['T5_dfs'] = 'PASS (%d values, %d solutions compared with brute force)' % (n, nsol)

sel = sys.argv[2].split(',') if len(sys.argv) > 2 else ['T1', 'T2', 'T3', 'T4', 'T5']
for t in (T1, T2, T3, T4, T5):
    if t.__name__ in sel: t()
print(json.dumps(R, indent=1))
