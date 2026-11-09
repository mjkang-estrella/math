"""Reviewer's own core routines (riordan-diameter-review-r1), written from the source definitions.

Conventions (CJKM v2 Def. 2.4 and eq. (4); Jung eq. (9)):
  * binary Bell matrix B = [b_{i,j}]_{i,j>=0} of (g, zg) with binary A-sequence (a_0=1, a_1, ...):
      b_{0,0} = 1,  b_{i+1,0} = sum_{m>=1} a_m b_{i,m-1},  b_{i+1,j+1} = sum_{m>=0} a_m b_{i,j+m}   (mod 2)
    i.e. uniformly b_{i+1,j} = sum_{m>=0} a_m b_{i,j-1+m} with b_{i,-1} = 0.
  * Riordan graph G_n on vertices 1..n: for i > j >= 1, i ~ j iff b_{i-2,j-1} = 1.
  * Power series over GF(2) are Python ints (bit t = coefficient of z^t).
Nothing here is imported from the discovery lane.
"""
import random


def popc(x):
    return x.bit_count()


def amask(a):
    m = 0
    for i, bit in enumerate(a):
        if bit:
            m |= 1 << i
    return m


def bell_rows(a, nrows):
    """Rows 0..nrows-1 of the binary Bell matrix with A-sequence a (list of bits, a[0] must be 1)."""
    A = amask(a)
    rows = [1]
    for i in range(nrows - 1):
        r = rows[-1]
        new = 0
        if popc(r & (A >> 1)) & 1:
            new |= 1
        for j in range(1, i + 2):
            if popc(r & (A << (j - 1))) & 1:
                new |= 1 << j
        rows.append(new)
    return rows


def graph_from_rows(rows, n):
    """Adjacency bitmasks adj[v] (v = 0..n-1 is vertex v+1) of G_n from Bell rows."""
    adj = [0] * n
    for i in range(2, n + 1):
        r = rows[i - 2]
        for j in range(1, i):
            if (r >> (j - 1)) & 1:
                adj[i - 1] |= 1 << (j - 1)
                adj[j - 1] |= 1 << (i - 1)
    return adj


def riordan_graph(a, n):
    """G_n(g, zg) for binary A-sequence prefix a (needs a[0..n-2])."""
    if n <= 1:
        return [0] * n
    a = list(a[: n - 1]) + [0] * max(0, n - 1 - len(a))
    return graph_from_rows(bell_rows(a, n - 1), n)


# ---------- independent power-series construction ----------

def clmul(x, y, t):
    """Product over GF(2), truncated mod z^t."""
    mask = (1 << t) - 1
    x &= mask
    y &= mask
    r = 0
    while y:
        low = y & -y
        s = low.bit_length() - 1
        r ^= (x << s)
        y ^= low
    return r & mask


def ps_inv(x, t):
    """Inverse of a GF(2) power series with constant term 1, mod z^t."""
    assert x & 1
    r = 1
    # naive long division
    for k in range(1, t):
        # coefficient k of x*r must vanish
        c = 0
        for i in range(1, k + 1):
            if (x >> i) & 1 and (r >> (k - i)) & 1:
                c ^= 1
        if c:
            r |= 1 << k
    return r


def compose(Amask_, h, t):
    """A(h) mod z^t for GF(2) series A (as int) and h with h(0)=0."""
    res = 0
    p = 1
    i = 0
    while (Amask_ >> i) and i < t:
        if (Amask_ >> i) & 1:
            res ^= p
        p = clmul(p, h, t)
        i += 1
        if p == 0:
            break
    return res


def solve_f(a, t):
    """f = z A(f) mod z^t by fixed-point iteration (t iterations suffice)."""
    A = amask(a)
    f = 0
    for _ in range(t + 1):
        nf = (compose(A, f, t - 1) << 1) & ((1 << t) - 1)
        if nf == f:
            break
        f = nf
    return f


def riordan_graph_ps(a, n):
    """G_n via eq. (4): for i > j, i ~ j iff [z^{i-1}] f^j = 1 (Bell type f = zg)."""
    f = solve_f(a, n)
    adj = [0] * n
    p = 1
    for j in range(1, n):
        p = clmul(p, f, n)  # f^j mod z^n
        for i in range(j + 1, n + 1):
            if (p >> (i - 1)) & 1:
                adj[i - 1] |= 1 << (j - 1)
                adj[j - 1] |= 1 << (i - 1)
    return adj


def riordan_graph_general(g, f, n):
    """General G_n(g, f): for i > j, i ~ j iff [z^{i-2}] g f^{j-1} = 1 (g, f as GF(2) ints)."""
    adj = [0] * n
    p = g & ((1 << n) - 1)
    for j in range(1, n):
        if j > 1:
            p = clmul(p, f, n)
        for i in range(j + 1, n + 1):
            if (p >> (i - 2)) & 1:
                adj[i - 1] |= 1 << (j - 1)
                adj[j - 1] |= 1 << (i - 1)
    return adj


# ---------- graph utilities ----------

def diameter(adj):
    """Exact diameter via ball growth; returns None if disconnected."""
    n = len(adj)
    if n <= 1:
        return 0
    full = (1 << n) - 1
    R = [(1 << v) | adj[v] for v in range(n)]
    nbrs = [[u for u in range(n) if (adj[v] >> u) & 1] for v in range(n)]
    t = 1
    while True:
        if all(r == full for r in R):
            return t
        newR = []
        for v in range(n):
            x = R[v]
            for u in nbrs[v]:
                x |= R[u]
            newR.append(x)
        if newR == R:
            return None
        R = newR
        t += 1


def distances_from(adj, s):
    n = len(adj)
    dist = [None] * n
    dist[s] = 0
    frontier = 1 << s
    seen = frontier
    d = 0
    while frontier:
        d += 1
        nxt = 0
        f = frontier
        while f:
            low = f & -f
            v = low.bit_length() - 1
            nxt |= adj[v]
            f ^= low
        nxt &= ~seen
        seen |= nxt
        f = nxt
        while f:
            low = f & -f
            v = low.bit_length() - 1
            dist[v] = d
            f ^= low
        frontier = nxt
    return dist


def induced(adj, verts):
    """Induced subgraph on the ordered vertex list verts (0-based), relabelled 0..len-1."""
    idx = {v: k for k, v in enumerate(verts)}
    out = []
    for v in verts:
        m = 0
        for u in verts:
            if (adj[v] >> u) & 1:
                m |= 1 << idx[u]
        out.append(m)
    return out


def edges(adj):
    return sum(popc(x) for x in adj) // 2


def io_sequences(nentries):
    """All io-decomposable Bell-type A-prefixes (a_0..a_{nentries-1}) per CJKM Thm 4.6:
    a_0 = a_1 = 1 and a_{2m+1} = a_{2m}."""
    free = list(range(2, nentries, 2))
    out = []
    for bits in range(1 << len(free)):
        a = [0] * nentries
        a[0] = 1
        if nentries > 1:
            a[1] = 1
        for t, p in enumerate(free):
            b = (bits >> t) & 1
            a[p] = b
            if p + 1 < nentries:
                a[p + 1] = b
        out.append(a)
    return out


def is_io_form(a):
    if a[0] != 1 or (len(a) > 1 and a[1] != 1):
        return False
    for m in range(1, (len(a) + 1) // 2):
        if 2 * m + 1 < len(a) and a[2 * m + 1] != a[2 * m]:
            return False
    return True


def random_io(nentries, rng):
    a = [0] * nentries
    a[0] = 1
    if nentries > 1:
        a[1] = 1
    for p in range(2, nentries, 2):
        b = rng.randrange(2)
        a[p] = b
        if p + 1 < nentries:
            a[p + 1] = b
    return a
