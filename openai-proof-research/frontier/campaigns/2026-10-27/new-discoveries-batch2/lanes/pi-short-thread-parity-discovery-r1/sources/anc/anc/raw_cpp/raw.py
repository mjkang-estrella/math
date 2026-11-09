"""Pure brute-force Game of Arrows solver, written directly from the raw rules.

A position on a tree: each edge is unmarked or oriented.  Edge i = (u_i, v_i);
we store a bitmask `marked` and a bitmask `dirm` (bit i = 0 means u_i -> v_i,
bit i = 1 means v_i -> u_i; dirm bits of unmarked edges are 0).
A move orients an unmarked edge; it is illegal if afterwards one of its two
endpoints has all its edges marked and all pointing in (sink) or all pointing
out (source).  Normal play.  No theory from the paper is used.
"""
import sys
sys.setrecursionlimit(10000)


class Arrows:
    def __init__(self, n, edges):
        self.n = n
        self.edges = list(edges)
        E = len(self.edges)
        self.E = E
        self.inc = [0] * n     # incident edge mask
        self.flip = [0] * n    # edges whose first endpoint is w
        for i, (u, v) in enumerate(self.edges):
            self.inc[u] |= 1 << i
            self.inc[v] |= 1 << i
            self.flip[u] |= 1 << i
        self.memo = {}

    def bad(self, w, marked, dirm):
        im = self.inc[w]
        if im == 0 or (marked & im) != im:
            return False
        x = (dirm ^ self.flip[w]) & im   # bit=0: edge points into w, 1: out of w
        return x == 0 or x == im

    def position(self, arcs):
        """arcs: list of (tail, head).  Returns (marked, dirm)."""
        idx = {}
        for i, (u, v) in enumerate(self.edges):
            idx[(u, v)] = (i, 0)
            idx[(v, u)] = (i, 1)
        marked = dirm = 0
        for t, h in arcs:
            i, d = idx[(t, h)]
            assert not (marked >> i) & 1
            marked |= 1 << i
            dirm |= d << i
        return marked, dirm

    def legal_position(self, marked, dirm):
        return not any(self.bad(w, marked, dirm) for w in range(self.n))

    def moves(self, marked, dirm):
        """Yield (i, tail, head, newmarked, newdirm) for legal moves."""
        for i in range(self.E):
            if (marked >> i) & 1:
                continue
            u, v = self.edges[i]
            nm = marked | (1 << i)
            for d in (0, 1):
                nd = dirm | (d << i)
                if self.bad(u, nm, nd) or self.bad(v, nm, nd):
                    continue
                yield (i, (u if d == 0 else v), (v if d == 0 else u), nm, nd)

    def g(self, marked=0, dirm=0):
        key = marked | (dirm << self.E)
        r = self.memo.get(key)
        if r is not None:
            return r
        opts = set()
        for (_, _, _, nm, nd) in self.moves(marked, dirm):
            opts.add(self.g(nm, nd))
        r = 0
        while r in opts:
            r += 1
        self.memo[key] = r
        return r


def grundy(n, edges, arcs=()):
    A = Arrows(n, edges)
    m, d = A.position(arcs)
    assert A.legal_position(m, d)
    return A.g(m, d)


def m_of(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return sum(1 for u, v in edges if deg[u] > 1 and deg[v] > 1)


# ---------------------------------------------------------------- tree builders
def spider(*legs):
    """Spider S(x1,...,xk): leg t is a path of x_t + 1 edges from centre 0.
    Returns (n, edges, legverts) where legverts[t] = [centre, v1, ..., v_{x_t+1}]."""
    n = 1
    edges = []
    legverts = []
    for x in legs:
        prev = 0
        lv = [0]
        for _ in range(x + 1):
            edges.append((prev, n))
            lv.append(n)
            prev = n
            n += 1
        legverts.append(lv)
    return n, edges, legverts


def Htree(a, b, l, c, d):
    """H(a,b|l|c,d): u,v joined by a path of l edges; u has legs a,b, v legs c,d
    (each leg = x markable edges + pendant edge)."""
    edges = []
    u = 0
    n = 1
    prev = u
    for _ in range(l):
        edges.append((prev, n))
        prev = n
        n += 1
    v = prev
    for root, x in ((u, a), (u, b), (v, c), (v, d)):
        p = root
        for _ in range(x + 1):
            edges.append((p, n))
            p = n
            n += 1
    return n, edges
