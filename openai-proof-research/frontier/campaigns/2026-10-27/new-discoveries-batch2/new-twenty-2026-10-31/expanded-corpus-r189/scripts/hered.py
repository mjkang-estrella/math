"""Minimal forbidden induced subgraphs for the hereditary class of
Henning-Jager-Rautenbach arXiv:1605.05056 (MathDB 333144):
  class = graphs G with gamma(H) = gamma_e(H) for every induced subgraph H.
Definitions exactly as in the source (Section 1): for D subset V, dist_(G,D)(u,v) is the
least length of a u-v path containing exactly one vertex of D as an endpoint and no
internal vertex of D; w(u) = sum_{v in D} (1/2)^(dist-1); D exponential dominating iff
w(u) >= 1 for all u.  (Equivalently: BFS from v in G - (D minus v); u in D gets 2.)
Level-by-level vertex extension: every graph on n vertices whose one-vertex-deleted
subgraphs are all class members arises as (member on n-1 vertices) + new vertex.
Isomorphism handled by a colour-refinement invariant plus explicit backtracking isomorphism.

usage: hered.py STATEDIR NMAX
writes STATEDIR/level-<n>.json  {"members": [...], "minimal_forbidden": [...]} (graphs as
lists of adjacency bitmasks), resumable level by level.
"""
import sys, json, itertools, pathlib, time

def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b

def dominating(adj, n, D):
    cov = 0
    for v in D:
        cov |= adj[v] | (1 << v)
    return cov == (1 << n) - 1

def gamma(adj, n):
    for k in range(1, n + 1):
        for D in itertools.combinations(range(n), k):
            if dominating(adj, n, D):
                return k
    return 0

def expdom(adj, n, D):
    Dmask = 0
    for v in D:
        Dmask |= 1 << v
    w = [0.0] * n
    for v in D:
        blocked = Dmask & ~(1 << v)
        # BFS from v avoiding other D-vertices
        dist = {v: 0}
        frontier = 1 << v
        seen = (1 << v) | blocked
        d = 0
        while frontier:
            d += 1
            nxt = 0
            for x in bits(frontier):
                nxt |= adj[x]
            nxt &= ~seen
            seen |= nxt
            for u in bits(nxt):
                w[u] += 2.0 ** (1 - d)
            frontier = nxt
        w[v] += 2.0
    return all(x >= 1.0 for x in w)

def gamma_e(adj, n, upto):
    for k in range(1, upto + 1):
        for D in itertools.combinations(range(n), k):
            if expdom(adj, n, D):
                return k
    return upto

def refine(adj, n):
    col = [bin(a).count('1') for a in adj]
    for _ in range(n):
        sig = [(col[v], tuple(sorted(col[u] for u in bits(adj[v])))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    return col, tuple(sorted(sig))

def invariant(adj, n):
    col, sig = refine(adj, n)
    return (n, sig), col

def iso(a, ca, b, cb, n):
    order = sorted(range(n), key=lambda v: (sum(1 for x in ca if x == ca[v]), ca[v]))
    m = {}
    used = 0
    def rec(i):
        nonlocal used
        if i == n:
            return True
        v = order[i]
        for t in range(n):
            if (used >> t) & 1 or cb[t] != ca[v]:
                continue
            ok = True
            for u, tu in m.items():
                if ((a[v] >> u) & 1) != ((b[t] >> tu) & 1):
                    ok = False; break
            if ok:
                m[v] = t; used |= 1 << t
                if rec(i + 1):
                    return True
                del m[v]; used &= ~(1 << t)
        return False
    return rec(0)

class Store:
    def __init__(self):
        self.b = {}
    def find(self, adj, n):
        key, col = invariant(adj, n)
        for (g, cg) in self.b.get(key, []):
            if iso(adj, col, g, cg, n):
                return g
        return None
    def add(self, adj, n):
        key, col = invariant(adj, n)
        lst = self.b.setdefault(key, [])
        for (g, cg) in lst:
            if iso(adj, col, g, cg, n):
                return False
        lst.append((tuple(adj), col))
        return True

def delete(adj, n, v):
    out = []
    for u in range(n):
        if u == v: continue
        a = adj[u]
        low = a & ((1 << v) - 1)
        high = (a >> (v + 1)) << v
        out.append(low | high)
    return out

if __name__ == '__main__':
    S = pathlib.Path(sys.argv[1]); S.mkdir(exist_ok=True)
    NMAX = int(sys.argv[2])
    t0 = time.time()
    lvl = {1: {'members': [[0]], 'minimal_forbidden': []}}
    for n in range(2, NMAX + 1):
        f = S / f'level-{n}.json'
        if f.exists():
            lvl[n] = json.loads(f.read_text()); continue
        prev = Store()
        for g in lvl[n - 1]['members']:
            prev.add(list(g), n - 1)
        cand = Store(); members, forb = [], []
        for h in lvl[n - 1]['members']:
            for S_ in range(1 << (n - 1)):
                adj = [h[u] | (((S_ >> u) & 1) << (n - 1)) for u in range(n - 1)] + [S_]
                if not cand.add(adj, n):
                    continue
                if any(prev.find(delete(adj, n, v), n - 1) is None for v in range(n - 1)):
                    continue
                g = gamma(adj, n)
                ge = gamma_e(adj, n, g)
                (members if ge == g else forb).append(adj)
        lvl[n] = {'members': members, 'minimal_forbidden': forb}
        f.write_text(json.dumps(lvl[n]))
        print('n', n, 'members', len(members), 'minimal forbidden', len(forb), 'elapsed', round(time.time() - t0, 1), flush=True)
