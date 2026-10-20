#!/usr/bin/env python3
"""Mechanical sanity checks for the r135 author proof (artifact checks, not a mathematical gate).

Run: python3 -B sanity.py
Covers items (a)-(h) listed in proof.md Section 12. Read-only; writes nothing.
"""
import itertools
import random
from fractions import Fraction

random.seed(20261020)


def d_r(r):
    return (r // 2) * ((r - 1) // 2)


def C2(x):
    return x * (x - 1) // 2


# (a) two forms of d_r
for r in range(1, 401):
    assert d_r(r) == C2(r // 2) + C2((r + 1) // 2), r

# (b) even-n deletion identity: n d_{n-1} = (n-2) d_n
for n in range(2, 401, 2):
    assert n * d_r(n - 1) == (n - 2) * d_r(n), n

# (c) rank-sum arithmetic: m^2 - m - 2 floor(m^2/4) = 2 d_m
for m in range(1, 401):
    assert m * m - m - 2 * ((m * m) // 4) == 2 * d_r(m), m

# (e) chord parity formula: sum of t over the four endpoint pairs == alternation bit, any gap
for order in itertools.permutations(range(4)):  # cyclic order of P1,P2,Q1,Q2 = 0,1,2,3
    pos = {v: i for i, v in enumerate(order)}
    # alternation on the circle: P's separate Q's
    cyc = list(order)
    def between(a, b, x):  # x strictly between a and b counterclockwise
        i, j = cyc.index(a), cyc.index(b)
        return (i < pos[x] < j) or (j < i and (pos[x] > i or pos[x] < j)) or (i > j and j < pos[x] < i)
    for gap in range(4):  # cut just before position `gap`
        lin = [cyc[(gap + k) % 4] for k in range(4)]
        lpos = {v: i for i, v in enumerate(lin)}
        s = sum(1 for u in (0, 1) for w in (2, 3) if lpos[u] < lpos[w]) % 2
        # alternation: exactly one Q on the ccw arc from P1 to P2 (independent of gap)
        arc = set()
        i, j = cyc.index(0), cyc.index(1)
        k = (i + 1) % 4
        while k != j:
            arc.add(cyc[k]); k = (k + 1) % 4
        alt = (len(arc & {2, 3}) == 1)
        assert s == int(alt), (order, gap)

# ---- GF(16) = GF(2)[x]/(x^4+x+1) ----
MOD = 0b10011


def gadd(a, b):
    return a ^ b


def gmul(a, b):
    p = 0
    while b:
        if b & 1:
            p ^= a
        b >>= 1
        a <<= 1
        if a & 0b10000:
            a ^= MOD
    return p & 0b1111


def gpow(a, e):
    r = 1
    while e:
        if e & 1:
            r = gmul(r, a)
        a = gmul(a, a)
        e >>= 1
    return r


def ginv(a):
    assert a != 0
    return gpow(a, 14)


def gdiv(a, b):
    return gmul(a, ginv(b))


def grank(M):  # rank over GF(16)
    M = [row[:] for row in M]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = ginv(M[r][c])
        M[r] = [gmul(x, inv) for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [gadd(x, gmul(f, y)) for x, y in zip(M[i], M[r])]
        r += 1
    return r


def g2rank(M):  # rank over GF(2)
    M = [row[:] for row in M]
    rows, cols = len(M), len(M[0])
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i][c]), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        for i in range(rows):
            if i != r and M[i][c]:
                M[i] = [x ^ y for x, y in zip(M[i], M[r])]
        r += 1
    return r


def make_detector(s, nodes):
    n = 2 * s + 1
    d = s * s
    assert len(nodes) == n and len(set(nodes)) == n
    # Pi(t) = prod (t - x_p) = prod (t + x_p) in char 2; coefficients low to high
    Pi = [1]
    for x in nodes:
        new = [0] * (len(Pi) + 1)
        for k, c in enumerate(Pi):
            new[k] ^= gmul(c, x)      # * x_p
            new[k + 1] ^= c           # * t
        Pi = new
    # formal derivative
    dPi = [gmul(Pi[k], k & 1) for k in range(1, len(Pi))]
    # Pi'(x_p) both ways
    for x in nodes:
        direct = 1
        for y in nodes:
            if y != x:
                direct = gmul(direct, gadd(x, y))
        formal = 0
        tp = 1
        for c in dPi:
            formal ^= gmul(c, tp)
            tp = gmul(tp, x)
        assert direct == formal and direct != 0
    PiP = [0] * n
    for p in range(n):
        PiP[p] = 1
        for k in range(n):
            if k != p:
                PiP[p] = gmul(PiP[p], gadd(nodes[p], nodes[k]))

    def h(p, q):
        return [gmul(gpow(nodes[p], a), gpow(nodes[q], b)) for a in range(s) for b in range(s)]

    def B(p, q):
        c = gdiv(gadd(nodes[p], nodes[q]), gmul(PiP[p], PiP[q]))
        hv = h(p, q)
        return [[gmul(c, gmul(hv[i], hv[j])) for j in range(d)] for i in range(d)]

    def Phi(H):
        out = [[0] * d for _ in range(d)]
        for p in range(n):
            for q in range(n):
                if H[p][q]:
                    Bpq = B(p, q)
                    for i in range(d):
                        for j in range(d):
                            out[i][j] ^= Bpq[i][j]
        return out

    return n, d, B, Phi, PiP, nodes


for s, nodes in ((1, [1, 2, 4]), (2, [1, 2, 4, 8, 3])):
    n, d, B, Phi, PiP, nds = make_detector(s, nodes)
    # (f) rank-one / zero-diagonal
    for p in range(n):
        assert grank(B(p, p)) == 0
        for q in range(n):
            if p != q:
                assert grank(B(p, q)) == 1
    # (f) additive and diagonal annihilation
    for _ in range(200):
        rv = [random.randint(0, 1) for _ in range(n)]
        cv = [random.randint(0, 1) for _ in range(n)]
        H = [[rv[p] ^ cv[q] for q in range(n)] for p in range(n)]
        assert grank(Phi(H)) == 0
        Hd = [[0] * n for _ in range(n)]
        for p in range(n):
            Hd[p][p] = random.randint(0, 1)
        assert grank(Phi(Hd)) == 0
    # (f) tournament invertibility for orders
    perms = list(itertools.permutations(range(n))) if n == 3 else \
        [tuple(random.sample(range(n), n)) for _ in range(40)]
    for perm in perms:  # perm lists elements in increasing <-order
        posi = {v: i for i, v in enumerate(perm)}
        T = [[1 if posi[p] < posi[q] else 0 for q in range(n)] for p in range(n)]
        assert grank(Phi(T)) == d, (s, perm)
    # (f) support bound on random H
    for _ in range(200):
        H = [[random.randint(0, 1) for _ in range(n)] for _ in range(n)]
        supp = sum(1 for p in range(n) for q in range(n) if p != q and H[p][q])
        assert grank(Phi(H)) <= supp
    # (h) barycentric identity: sum_p A(x_p)/Pi'(x_p) = 0 for deg A <= n-2
    for _ in range(200):
        A = [random.randint(0, 15) for _ in range(n - 1)]  # deg <= n-2
        tot = 0
        for p in range(n):
            v = 0
            tp = 1
            for c in A:
                v ^= gmul(c, tp)
                tp = gmul(tp, nds[p])
            tot ^= gdiv(v, PiP[p])
        assert tot == 0

# (g) Corollary 6 over GF(2)
for m in (3, 4, 5, 6):
    for dd in (1, 2, 3):
        target = 2 * d_r(m) * dd
        for _ in range(200):
            X = [[[random.randint(0, 1) for _ in range(dd)] for _ in range(dd)] for _ in range(m)]
            Y = []
            for i in range(m):
                while True:
                    Yi = [[random.randint(0, 1) for _ in range(dd)] for _ in range(dd)]
                    if g2rank([[X[i][a][b] ^ Yi[a][b] for b in range(dd)] for a in range(dd)]) == dd:
                        Y.append(Yi)
                        break
            tot = 0
            for i in range(m):
                for k in range(m):
                    if i != k:
                        tot += g2rank([[X[i][a][b] ^ Y[k][a][b] for b in range(dd)]
                                       for a in range(dd)])
            assert tot >= target, (m, dd)

# (d) exact axis-drawing simulation
def seg_cross(v1, h1, v2, h2):
    """Proper interior crossing of segments (0,v1)-(h1,0) and (0,v2)-(h2,0), exact."""
    if v1 == v2 or h1 == h2:
        return None
    den = v1 * h2 - h1 * v2
    if den == 0:
        return None  # parallel; distinct intercepts keep pairs non-collinear
    t = Fraction(h2 * (v1 - v2), den)
    s = Fraction(h1 * (v1 - v2), den)
    if 0 < t < 1 and 0 < s < 1:
        return (t * h1, (1 - t) * v1)
    return None


for m in range(2, 8):
    for n in range(2, 8):
        vp = [2 ** (i + 1) for i in range((m + 1) // 2)]
        vn = [-(3 ** (i + 1)) for i in range(m // 2)]
        hp = [5 ** (j + 1) for j in range((n + 1) // 2)]
        hn = [-(7 ** (j + 1)) for j in range(n // 2)]
        Vs = vp + vn
        Hs = hp + hn
        cross_pts = {}
        total = 0
        for (i1, v1) in enumerate(Vs):
            for (i2, v2) in enumerate(Vs):
                if i2 <= i1:
                    continue
                for (j1, h1) in enumerate(Hs):
                    for (j2, h2) in enumerate(Hs):
                        if j2 <= j1:
                            continue
                        for w1, w2 in ((h1, h2), (h2, h1)):  # both matchings of the 4-set
                            pt = seg_cross(v1, w1, v2, w2)
                            if pt is not None:
                                total += 1
                                cross_pts.setdefault(pt, []).append((i1, j1, i2, j2))
        # count every independent edge pair, check <= 1 crossing, adjacency free
        edges = [(i, j) for i in range(m) for j in range(n)]
        allv = Vs
        allh = Hs
        cnt = 0
        for e1 in range(len(edges)):
            for e2 in range(e1 + 1, len(edges)):
                i1, j1 = edges[e1]
                i2, j2 = edges[e2]
                pt = seg_cross(allv[i1], allh[j1], allv[i2], allh[j2])
                if i1 == i2 or j1 == j2:
                    assert pt is None, "adjacent edges cross"
                else:
                    cnt += (pt is not None)
        assert cnt == d_r(m) * d_r(n), (m, n, cnt)
        assert all(len(v) == 1 for v in cross_pts.values()), "triple concurrence"
        assert total == cnt

print("SANITY OK: checks (a)-(h) passed")
