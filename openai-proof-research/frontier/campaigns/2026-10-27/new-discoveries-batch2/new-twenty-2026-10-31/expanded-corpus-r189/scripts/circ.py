"""Scan circulant graphs C_n(S) for minimal forbidden induced subgraphs of the
hereditary class gamma = gamma_e (MathDB 333144).
A circulant G is minimal forbidden iff gamma(G) != gamma_e(G) and every induced subgraph
G[X], X a subset of V minus {0} (vertex transitivity), has gamma = gamma_e.  Subsets of size
<= 5 are skipped: the level search (hered.py) found no minimal forbidden graph on <= 5 vertices.
usage: circ.py N  (all connection sets S of {1..N/2}, up to multiplier equivalence)
"""
import sys, itertools, math, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from hered import gamma, gamma_e

def circ(n, S):
    adj = [0] * n
    for i in range(n):
        for s in S:
            for j in ((i + s) % n, (i - s) % n):
                if j != i: adj[i] |= 1 << j
    return adj

def induced(adj, X):
    idx = {v: k for k, v in enumerate(X)}
    out = []
    for v in X:
        m = 0
        for u in X:
            if adj[v] >> u & 1: m |= 1 << idx[u]
        out.append(m)
    return out

def connected(adj, n):
    seen, fr = 1, 1
    while fr:
        nx = 0
        for v in range(n):
            if fr >> v & 1: nx |= adj[v]
        fr = nx & ~seen; seen |= nx
    return seen == (1 << n) - 1

def hered_ok(adj, n):
    for k in range(6, n):
        for X in itertools.combinations(range(1, n), k):
            h = induced(adj, X)
            g = gamma(h, k)
            if gamma_e(h, k, g) != g:
                return False, X
    return True, None

n = int(sys.argv[1])
units = [m for m in range(1, n) if math.gcd(m, n) == 1]
seen = set(); found = []
for r in range(1, n // 2 + 1):
    for S in itertools.combinations(range(1, n // 2 + 1), r):
        key = min(tuple(sorted({min((m * s) % n, n - (m * s) % n) for s in S})) for m in units)
        if key in seen: continue
        seen.add(key)
        adj = circ(n, S)
        if not connected(adj, n): continue
        g = gamma(adj, n); ge = gamma_e(adj, n, g)
        if g == ge: continue
        ok, X = hered_ok(adj, n)
        print('n', n, 'S', S, 'deg', bin(adj[0]).count('1'), 'gamma', g, 'gamma_e', ge, 'MINIMAL' if ok else 'not minimal (bad induced subgraph on %d vertices)' % len(X), flush=True)
        if ok: found.append(S)
print('n', n, 'classes', len(seen), 'minimal forbidden circulants:', found)
