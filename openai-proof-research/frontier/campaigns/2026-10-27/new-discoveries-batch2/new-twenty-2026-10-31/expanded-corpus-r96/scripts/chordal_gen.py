"""Generate all unlabeled chordal graphs on n <= NMAX vertices (connected or not).

Every chordal graph has a simplicial vertex, so chordal(n) = { G + v, N(v) a clique of G : G in chordal(n-1) }.
Isomorphism classes are separated by an invariant (colour refinement histogram) plus an exact
backtracking isomorphism test.  Graphs are stored as tuples of adjacency bitmasks.
Output: outputs/chordal/chordal-n{n}.json  (list of adjacency tuples), counts checked against
OEIS A058862 (all) and A048193 (connected).
usage: chordal_gen.py NMAX
"""
import sys, json, resource, pathlib
resource.setrlimit(resource.RLIMIT_CPU, (118, 118))
L = pathlib.Path(__file__).resolve().parents[1]
OUT = L / 'outputs' / 'chordal'; OUT.mkdir(parents=True, exist_ok=True)

def refine(adj, n, colors):
    while True:
        sig = [(colors[v], tuple(sorted(colors[u] for u in range(n) if adj[v] >> u & 1))) for v in range(n)]
        keys = sorted(set(sig)); new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(colors)):
            return new
        colors = new

def invariant(adj):
    n = len(adj)
    c = refine(adj, n, [0] * n)
    # histogram of (final colour signature) is isomorphism invariant only if colour names are canonical:
    # recompute canonical names from signatures in refinement order
    cols = [0] * n; hist = []
    for _ in range(n + 1):
        sig = [(cols[v], tuple(sorted(cols[u] for u in range(n) if adj[v] >> u & 1))) for v in range(n)]
        keys = sorted(set(sig)); new = [keys.index(s) for s in sig]
        hist.append(tuple(sorted(sig)))
        if new == cols: break
        cols = new
    return (n, sum(bin(a).count('1') for a in adj) // 2, tuple(hist))

def isomorphic(A, B):
    n = len(A)
    if n != len(B): return False
    ca = refine(A, n, [0] * n); cb = refine(B, n, [0] * n)
    # colour classes must be matched by signature, so recompute with joint naming
    def joint(adjX, adjY):
        cx = [0] * n; cy = [0] * n
        while True:
            sx = [(cx[v], tuple(sorted(cx[u] for u in range(n) if adjX[v] >> u & 1))) for v in range(n)]
            sy = [(cy[v], tuple(sorted(cy[u] for u in range(n) if adjY[v] >> u & 1))) for v in range(n)]
            if sorted(sx) != sorted(sy): return None
            keys = sorted(set(sx)); nx = [keys.index(s) for s in sx]; ny = [keys.index(s) for s in sy]
            if nx == cx and ny == cy: return cx, cy
            cx, cy = nx, ny
    j = joint(A, B)
    if j is None: return False
    cx, cy = j
    order = sorted(range(n), key=lambda v: (sum(1 for w in range(n) if cx[w] == cx[v]), cx[v]))
    m = {}; used = set()
    def bt(i):
        if i == n: return True
        v = order[i]
        for w in range(n):
            if w in used or cy[w] != cx[v]: continue
            ok = True
            for u, x in m.items():
                if ((A[v] >> u) & 1) != ((B[w] >> x) & 1): ok = False; break
            if ok:
                m[v] = w; used.add(w)
                if bt(i + 1): return True
                del m[v]; used.discard(w)
        return False
    return bt(0)

class Store:
    def __init__(self): self.d = {}; self.items = []
    def find(self, adj):
        key = invariant(adj)
        for idx in self.d.get(key, []):
            if isomorphic(self.items[idx], adj): return idx
        return None
    def add(self, adj):
        idx = self.find(adj)
        if idx is not None: return idx, False
        key = invariant(adj)
        self.items.append(tuple(adj)); self.d.setdefault(key, []).append(len(self.items) - 1)
        return len(self.items) - 1, True

def cliques(adj):
    n = len(adj); out = [0]
    def ext(cl, cand):
        for v in cand:
            nc = cl | (1 << v); out.append(nc)
            ext(nc, [u for u in cand if u > v and adj[v] >> u & 1])
    ext(0, list(range(n)))
    return out

def connected(adj):
    n = len(adj)
    if n == 0: return True
    seen = 1; frontier = 1
    while frontier:
        nb = 0
        for v in range(n):
            if frontier >> v & 1: nb |= adj[v]
        frontier = nb & ~seen; seen |= nb
    return seen == (1 << n) - 1

A058862 = [1, 2, 4, 10, 27, 94, 393, 2119, 14524, 126758]
A048193 = [1, 1, 2, 5, 15, 58, 272, 1614, 11911, 109539]

if __name__ == '__main__':
    NMAX = int(sys.argv[1])
    prev = [()]  # n = 0
    start = 1
    for n in range(1, NMAX + 1):
        f = OUT / f'chordal-n{n}.json'
        if f.exists():
            prev = [tuple(g) for g in json.loads(f.read_text())]; continue
        st = Store()
        for G in prev:
            for cl in cliques(list(G)):
                adj = list(G) + [cl]
                for u in range(n - 1):
                    if cl >> u & 1: adj[u] |= 1 << (n - 1)
                st.add(adj)
        prev = st.items
        conn = sum(1 for g in prev if connected(g))
        f.write_text(json.dumps(prev))
        print(json.dumps({'n': n, 'all': len(prev), 'connected': conn, 'oeis_all': A058862[n - 1], 'oeis_connected': A048193[n - 1],
                          'match': len(prev) == A058862[n - 1] and conn == A048193[n - 1]}), flush=True)
