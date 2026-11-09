"""Independent outer-connected domination tools (middle-review-r1).

Written from the source definitions only (arXiv:2206.15439v1, Definitions 1.2 and 1.3):
  * S is dominating if every vertex is in S or has a neighbour in S;
  * S is outer-connected dominating (OCD) if S is dominating and G - S is connected;
  * M(G) has vertex set V(G) u E(G); an edge node is adjacent to its two endpoints and to every
    other edge sharing an endpoint; two vertex nodes are never adjacent.
Conventions for an empty complement G - S:
  'A' : the empty graph counts as connected (so S = V is always OCD);
  'B' : G - S must be non-empty and connected.
No code from the discovery lane is imported or copied.
"""
from itertools import combinations

# ---------------------------------------------------------------- basic graph ops

def popcount(x):
    return bin(x).count("1")


def from_edges(n, edges):
    adj = [0] * n
    for a, b in edges:
        assert a != b
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def edges_of(n, adj):
    return [(a, b) for a in range(n) for b in range(a + 1, n) if adj[a] >> b & 1]


def is_connected_mask(adj, mask, conv):
    """Is the subgraph induced on the node set `mask` connected?"""
    if mask == 0:
        return conv == "A"
    start = mask & -mask
    seen = start
    frontier = start
    while frontier:
        low = frontier & -frontier
        v = low.bit_length() - 1
        frontier ^= low
        new = adj[v] & mask & ~seen
        seen |= new
        frontier |= new
    return seen == mask


def is_dominating(adj, S, full):
    """closed-neighbourhood domination of every node in `full` by S."""
    rest = full & ~S
    while rest:
        low = rest & -rest
        v = low.bit_length() - 1
        rest ^= low
        if adj[v] & S == 0:
            return False
    return True


def is_ocd(adj, N, S, conv):
    full = (1 << N) - 1
    return is_dominating(adj, S, full) and is_connected_mask(adj, full & ~S, conv)


_MASKS = {}


def masks_by_size(N):
    if N not in _MASKS:
        _MASKS[N] = sorted(range(1 << N), key=lambda m: (popcount(m), m))
    return _MASKS[N]


def ocd_bruteforce(adj, N, conv):
    """Minimum OCD size by enumerating all 2^N subsets in order of size (None if none)."""
    for S in masks_by_size(N):
        if is_ocd(adj, N, S, conv):
            return popcount(S)
    return None


def all_min_ocd(adj, N, conv):
    best = None
    out = []
    for S in masks_by_size(N):
        c = popcount(S)
        if best is not None and c > best:
            break
        if is_ocd(adj, N, S, conv):
            best = c
            out.append(S)
    return best, out

# ---------------------------------------------------------------- middle graph

def middle(n, adj):
    """Return (N, madj, edge_list): node i < n is vertex i, node n+j is edge j."""
    E = edges_of(n, adj)
    N = n + len(E)
    madj = [0] * N
    for j, (a, b) in enumerate(E):
        e = n + j
        madj[e] |= (1 << a) | (1 << b)
        madj[a] |= 1 << e
        madj[b] |= 1 << e
    for j, (a, b) in enumerate(E):
        for k in range(j + 1, len(E)):
            c, d = E[k]
            if a in (c, d) or b in (c, d):
                madj[n + j] |= 1 << (n + k)
                madj[n + k] |= 1 << (n + j)
    return N, madj, E


def closed_nbhd(adj, v):
    return adj[v] | (1 << v)


def exists_ocd_of_size(adj, N, t, conv):
    """Exact: is there an OCD set of size exactly t?  Branch on the undominated node with the
    smallest closed neighbourhood (some element of that neighbourhood lies in any dominating set);
    at a dominating partial set C, try every superset of size t.  Returns a witness mask or None."""
    full = (1 << N) - 1
    cn = [closed_nbhd(adj, v) for v in range(N)]
    tried = set()

    def rec(C, size):
        # undominated nodes
        dom = 0
        m = C
        while m:
            low = m & -m
            dom |= cn[low.bit_length() - 1]
            m ^= low
        und = full & ~dom
        if und == 0:
            if C in tried:
                return None
            tried.add(C)
            rest = [v for v in range(N) if not C >> v & 1]
            for extra in combinations(rest, t - size):
                D = C
                for v in extra:
                    D |= 1 << v
                if is_connected_mask(adj, full & ~D, conv):
                    return D
            return None
        if size == t:
            return None
        # pick undominated node with smallest closed neighbourhood
        best = None
        bc = None
        m = und
        while m:
            low = m & -m
            v = low.bit_length() - 1
            m ^= low
            c = popcount(cn[v])
            if bc is None or c < bc:
                best, bc = v, c
        nb = cn[best]
        while nb:
            low = nb & -nb
            nb ^= low
            r = rec(C | low, size + 1)
            if r is not None:
                return r
        return None

    return rec(0, 0)


def ocd_branch(adj, N, conv, cap=None):
    """Minimum OCD size by the exact branching search, up to `cap` (None if none <= cap)."""
    top = N if cap is None else min(cap, N)
    for t in range(0, top + 1):
        if exists_ocd_of_size(adj, N, t, conv) is not None:
            return t
    return None

# ---------------------------------------------------------------- matchings

def perfect_matchings(n, adj):
    """All perfect matchings as lists of edges (a,b), a<b."""
    out = []

    def rec(free, cur):
        if free == 0:
            out.append(list(cur))
            return
        low = free & -free
        a = low.bit_length() - 1
        nb = adj[a] & free
        while nb:
            lb = nb & -nb
            b = lb.bit_length() - 1
            nb ^= lb
            cur.append((a, b))
            rec(free & ~low & ~lb, cur)
            cur.pop()

    rec((1 << n) - 1, [])
    return out


def remove_edges(n, adj, F):
    a2 = list(adj)
    for a, b in F:
        a2[a] &= ~(1 << b)
        a2[b] &= ~(1 << a)
    return a2

# ---------------------------------------------------------------- isomorphism handling

def wl_invariant(n, adj):
    """Colour refinement started from (degree, triangles at v).  Returns (invariant, colours)
    where colours are canonical integers comparable between graphs with equal invariant."""
    deg = [popcount(adj[v]) for v in range(n)]
    tri = []
    for v in range(n):
        t = 0
        nb = adj[v]
        m = nb
        while m:
            low = m & -m
            u = low.bit_length() - 1
            m ^= low
            t += popcount(adj[u] & nb)
        tri.append(t // 2)
    sig = [(deg[v], tri[v]) for v in range(n)]
    hist = []
    for _ in range(n + 1):
        keys = sorted(set(sig))
        idx = {k: i for i, k in enumerate(keys)}
        col = [idx[s] for s in sig]
        hist.append(tuple(keys))
        nsig = []
        for v in range(n):
            nbc = []
            m = adj[v]
            while m:
                low = m & -m
                nbc.append(col[low.bit_length() - 1])
                m ^= low
            nsig.append((col[v], tuple(sorted(nbc))))
        if len(set(nsig)) == len(keys):
            break
        sig = nsig
    return (n, tuple(hist)), col


def isomorphic(n, adj1, col1, adj2, col2):
    """Backtracking isomorphism test respecting the refined colours."""
    order = sorted(range(n), key=lambda v: (sum(1 for u in range(n) if col1[u] == col1[v]), v))
    f = [-1] * n
    used = [False] * n

    def rec(i):
        if i == n:
            return True
        v = order[i]
        for w in range(n):
            if used[w] or col2[w] != col1[v]:
                continue
            ok = True
            for j in range(i):
                u = order[j]
                if (adj1[v] >> u & 1) != (adj2[w] >> f[u] & 1):
                    ok = False
                    break
            if ok:
                f[v] = w
                used[w] = True
                if rec(i + 1):
                    return True
                used[w] = False
                f[v] = -1
        return False

    return rec(0)


def encode(n, adj):
    """Upper-triangle bit encoding (pair (a,b), a<b, in lexicographic order)."""
    code = 0
    bit = 0
    for a in range(n):
        for b in range(a + 1, n):
            if adj[a] >> b & 1:
                code |= 1 << bit
            bit += 1
    return code


def decode(n, code):
    adj = [0] * n
    bit = 0
    for a in range(n):
        for b in range(a + 1, n):
            if code >> bit & 1:
                adj[a] |= 1 << b
                adj[b] |= 1 << a
            bit += 1
    return adj


def is_connected_graph(n, adj):
    return n >= 1 and is_connected_mask(adj, (1 << n) - 1, "B")
