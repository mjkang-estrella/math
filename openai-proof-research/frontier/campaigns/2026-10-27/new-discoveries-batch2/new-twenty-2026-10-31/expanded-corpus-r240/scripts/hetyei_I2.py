"""347230/347231: Hetyei's interval transform of the second kind I2 on Q<a,b>_n, computed in the
flag-f basis (Psi = sum_S f(S) w_S, w_S has b at positions in S and (a-b) elsewhere).
For a graded poset P of rank n+1:  Psi_{I2(P)} = sum_{x in P} Psi_{[0,x]^* x [x,1]}.
Flag f of a product of two chain-supported pieces = Delannoy paths (steps (1,0),(0,1),(1,1)).
Mode 'check': brute-force comparison with explicit posets for small n.
Mode 'rank N P': rank of I2 restricted to symmetric subspace mod prime P, for n = 1..N.
Usage: hetyei_I2.py check | hetyei_I2.py rank NMAX PRIME"""
import sys, itertools
from functools import lru_cache

def bits(mask, n): return [i + 1 for i in range(n) if mask >> i & 1]
def tomask(s):
    m = 0
    for i in s: m |= 1 << (i - 1)
    return m

@lru_cache(None)
def delannoy_sets(R1, R2):
    """R1, R2: tuples of ranks of the chain elements 0=R[0]<...<R[-1] (top). Return dict
    mask -> count over Delannoy paths of intermediate rank sets (rank of (a,b) = R1[a]+R2[b])."""
    A, B = len(R1) - 1, len(R2) - 1
    # dp over grid points: dict of mask->count for paths from (0,0) to (a,b), mask of intermediate points incl (a,b)
    dp = {}
    for a in range(A + 1):
        for b in range(B + 1):
            if a == 0 and b == 0:
                dp[(0, 0)] = {0: 1}; continue
            cur = {}
            for da, db in ((1, 0), (0, 1), (1, 1)):
                pa, pb = a - da, b - db
                if pa < 0 or pb < 0: continue
                for m, c in dp[(pa, pb)].items():
                    cur[m] = cur.get(m, 0) + c
            if (a, b) != (A, B):
                bit = 1 << (R1[a] + R2[b] - 1)
                cur = {m | bit: c for m, c in cur.items()}
            dp[(a, b)] = cur
    return dp[(A, B)]

def I2_column(T, n):
    """I2 applied to the flag-f basis vector delta_T; returns dict mask->coeff."""
    out = {}
    def addm(m, c): out[m] = out.get(m, 0) + c
    Ts = bits(T, n)
    addm(T, 1)
    addm(tomask([n + 1 - i for i in Ts]), 1)
    for r in Ts:
        low = [i for i in Ts if i < r]; high = [i for i in Ts if i > r]
        I1 = sorted(r - i for i in low)          # ranks in [0,x]^* (rank r)
        J1 = sorted(i - r for i in high)         # ranks in [x,1] (rank n+1-r)
        R1 = tuple([0] + I1 + [r]); R2 = tuple([0] + J1 + [n + 1 - r])
        for m, c in delannoy_sets(R1, R2).items():
            addm(m, c)
    return out

def check():
    # explicit posets: Boolean algebras B_k, chains, and a few random graded posets
    import random
    random.seed(1)
    def flagf(elems, rank, leq, top):
        n = rank[top] - 1
        res = {}
        inner = [e for e in elems if 0 < rank[e] < rank[top]]
        def rec(last, mask):
            res[mask] = res.get(mask, 0) + 1
            for e in inner:
                if rank[e] > rank[last] and leq(last, e):
                    rec(e, mask | 1 << (rank[e] - 1))
        bot = [e for e in elems if rank[e] == 0][0]
        rec(bot, 0)
        return res, n
    def random_graded(nr, width):
        levels = [[(0, 0)]] + [[(k, j) for j in range(random.randint(1, width))] for k in range(1, nr)] + [[(nr, 0)]]
        cover = set()
        for k in range(nr):
            for y in levels[k + 1]:
                for x in levels[k]:
                    if random.random() < 0.6: cover.add((x, y))
                # ensure each y has a lower cover
                if not any((x, y) in cover for x in levels[k]): cover.add((random.choice(levels[k]), y))
            for x in levels[k]:
                if not any((x, y) in cover for y in levels[k + 1]): cover.add((x, random.choice(levels[k + 1])))
        elems = [e for L in levels for e in L]
        up = {e: {e} for e in elems}
        for k in range(nr - 1, -1, -1):
            for x in levels[k]:
                for y in levels[k + 1]:
                    if (x, y) in cover: up[x] |= up[y]
        return elems, {e: e[0] for e in elems}, (lambda x, y: y in up[x]), (nr, 0)
    tests = []
    for nr in range(2, 6):
        for _ in range(4):
            tests.append(random_graded(nr, 3))
    for k in range(1, 5):  # Boolean algebra
        elems = list(range(1 << k)); tests.append((elems, {e: bin(e).count('1') for e in elems}, (lambda x, y: x & y == x), (1 << k) - 1))
    bad = 0
    for elems, rank, leq, top in tests:
        fP, n = flagf(elems, rank, leq, top)
        # predicted
        pred = {}
        for T, c in fP.items():
            for m, d in I2_column(T, n).items():
                pred[m] = pred.get(m, 0) + c * d
        # explicit: sum over x of [x,x] .. [0,1] in interval poset = pairs (y,z), y<=x<=z, ordered by containment
        bot = [e for e in elems if rank[e] == 0][0]
        expl = {}
        for x in elems:
            pts = [(y, z) for y in elems for z in elems if leq(y, x) and leq(x, z)]
            rk = {p: (rank[x] - rank[p[0]]) + (rank[p[1]] - rank[x]) for p in pts}
            lq = lambda p, q: leq(q[0], p[0]) and leq(p[1], q[1])
            f, n2 = flagf(pts, rk, lq, (bot, top))
            assert n2 == n
            for m, c in f.items(): expl[m] = expl.get(m, 0) + c
        pred = {m: c for m, c in pred.items() if c}; expl = {m: c for m, c in expl.items() if c}
        if pred != expl:
            bad += 1; print('MISMATCH n', n, pred, expl)
    print('check posets', len(tests), 'mismatches', bad)

def rank_sym(n, p):
    N = 1 << n
    rev = lambda m: tomask([n + 1 - i for i in bits(m, n)])
    # symmetric basis: e_T + e_{T*} for orbit representatives
    reps = sorted({min(m, rev(m)) for m in range(N)})
    rows = []
    for T in reps:
        v = dict(I2_column(T, n))
        if rev(T) != T:
            for m, c in I2_column(rev(T), n).items(): v[m] = v.get(m, 0) + c
        rows.append([v.get(m, 0) % p for m in range(N)])
    # rank mod p of the list of image vectors
    rk = 0; ncols = N; rowsl = rows
    for col in range(ncols):
        piv = None
        for i in range(rk, len(rowsl)):
            if rowsl[i][col]: piv = i; break
        if piv is None: continue
        rowsl[rk], rowsl[piv] = rowsl[piv], rowsl[rk]
        pr = rowsl[rk]; inv = pow(pr[col], p - 2, p)
        pr = [(x * inv) % p for x in pr]; rowsl[rk] = pr
        for i in range(rk + 1, len(rowsl)):
            c = rowsl[i][col]
            if c:
                ri = rowsl[i]
                rowsl[i] = [(x - c * y) % p for x, y in zip(ri, pr)]
        rk += 1
    return rk, len(reps)

if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check()
    else:
        nmax, p = int(sys.argv[2]), int(sys.argv[3])
        nmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        for n in range(nmin, nmax + 1):
            rk, d = rank_sym(n, p)
            print('n', n, 'dim S_n', d, 'rank of I2 on S_n mod', p, '=', rk, 'injective' if rk == d else 'NOT INJECTIVE mod p', flush=True)
