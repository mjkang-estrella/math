"""Exhaustive enumeration of unlabeled cographs (canonical cotrees) up to order N, exact cotree DP for
(inf,k)- and (1,k)-polarity, and census of cograph minimal (inf,k)-polar obstructions by type (c,i).

Definitions (Contreras-Mendoza & Hernandez-Cruz, arXiv:2104.07852): an (s,k)-polar partition (A,B) of V(G):
A induces a complete multipartite graph with at most s parts, B induces a disjoint union of at most k cliques
(a cluster).  Empty A or B allowed.  Minimal obstruction: not (inf,k)-polar, every one-vertex-deleted
induced subgraph is (inf,k)-polar (cographs are hereditary, so vertex deletions suffice).
Type (c,i): c components, i of them isolated vertices.

Cotree canonical form: 'v' (vertex); ('U', children) disjoint union of >=2 connected children;
('J', children) join of >=2 co-connected children; children tuples sorted by key.

DP state per graph: set of (a,b) where a in {0: A empty, 1: A nonempty edgeless, 2: A complete multipartite
with an edge} and b = number of cliques of the cluster B (capped at CAP meaning ">= CAP").
Union: A1 u A2 complete multipartite iff one empty or both edgeless; B cliques add.
Join: A1 + A2 always complete multipartite (a = 2 if both nonempty); B1 join B2 a cluster iff one empty
or both single cliques (then b = 1).

Self-check: brute-force polarity on explicit adjacency for all cographs of order <= BRUTE.
Usage: polar_cographs.py N KMAX BRUTE OUT_JSON
"""
import sys, json, itertools
from functools import lru_cache
N, KMAX, BRUTE, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
CAP = KMAX + 2
V = 'v'

def key(g):
    return repr(g)

def mk(typ, children):
    ch = []
    for c in children:
        if c != V and c[0] == typ:
            ch.extend(c[1])
        else:
            ch.append(c)
    if len(ch) == 1:
        return ch[0]
    return (typ, tuple(sorted(ch, key=key)))

@lru_cache(maxsize=None)
def size(g):
    return 1 if g == V else sum(size(c) for c in g[1])

# generation by size: conn[n] = connected (J-rooted or vertex), disc[n] = disconnected (U-rooted)
conn = {1: [V]}; disc = {1: []}
def multisets(pools, n, minparts):
    """All multisets of objects (from pools[size] lists) with total size n and >= minparts parts.
    Generated as non-increasing sequences of (size, index)."""
    out = []
    def rec(rem, maxitem, acc):
        if rem == 0:
            if len(acc) >= minparts:
                out.append(list(acc))
            return
        for s in range(min(rem, maxitem[0]), 0, -1):
            lst = pools.get(s, [])
            top = min(maxitem[1], len(lst) - 1) if s == maxitem[0] else len(lst) - 1
            for idx in range(top, -1, -1):
                acc.append(lst[idx]); rec(rem - s, (s, idx), acc); acc.pop()
    rec(n, (n, 10 ** 9), [])
    return out
for n in range(2, N + 1):
    coconn = {s: ([V] if s == 1 else disc[s]) for s in range(1, n)}
    conn[n] = [('J', tuple(sorted(ms, key=key))) for ms in multisets(coconn, n, 2)]
    cpool = {s: conn[s] for s in range(1, n)}
    disc[n] = [('U', tuple(sorted(ms, key=key))) for ms in multisets(cpool, n, 2)]

@lru_cache(maxsize=None)
def states(g):
    if g == V:
        return frozenset({(1, 0), (0, 1)})
    typ, ch = g
    cur = states(ch[0])
    for c in ch[1:]:
        nxt = set()
        for (a1, b1) in cur:
            for (a2, b2) in states(c):
                if typ == 'U':
                    if a1 == 0: a = a2
                    elif a2 == 0: a = a1
                    elif a1 == 1 and a2 == 1: a = 1
                    else: continue
                    b = min(CAP, b1 + b2)
                else:
                    a = a2 if a1 == 0 else (a1 if a2 == 0 else 2)
                    if b1 == 0: b = b2
                    elif b2 == 0: b = b1
                    elif b1 == 1 and b2 == 1: b = 1
                    else: continue
                nxt.add((a, b))
        cur = frozenset(nxt)
    return cur

def polar_inf(g, k):
    return any(b <= k for (a, b) in states(g))
def polar_one(g, k):
    return any(a <= 1 and b <= k for (a, b) in states(g))

@lru_cache(maxsize=None)
def deletions(g):
    if g == V:
        return frozenset({None})
    typ, ch = g
    res = set()
    for idx, c in enumerate(ch):
        if idx > 0 and ch[idx - 1] == c:
            continue
        rest = list(ch[:idx]) + list(ch[idx + 1:])
        for d in deletions(c):
            res.add(mk(typ, rest + ([] if d is None else [d])))
    return frozenset(res)

def components(g):
    if g == V: return [V]
    return list(g[1]) if g[0] == 'U' else [g]

def show(g):
    if g == V: return 'K1'
    sep = ' + ' if g[0] == 'U' else ' (+) '
    return '(' + sep.join(show(c) for c in g[1]) + ')'

# explicit adjacency for brute-force check
def explicit(g):
    if g == V: return 1, set()
    typ, ch = g
    n = 0; E = set(); parts = []
    for c in ch:
        m, e = explicit(c)
        E |= {(u + n, w + n) for (u, w) in e}; parts.append(range(n, n + m)); n += m
    if typ == 'J':
        for p, q in itertools.combinations(parts, 2):
            E |= {(min(u, w), max(u, w)) for u in p for w in q}
    return n, {(min(u, w), max(u, w)) for (u, w) in E}

def brute(g, s_one, k):
    n, E = explicit(g)
    adj = lambda u, w: (min(u, w), max(u, w)) in E
    for mask in range(1 << n):
        A = [v for v in range(n) if mask >> v & 1]; B = [v for v in range(n) if not mask >> v & 1]
        # A complete multipartite: nonadjacency is an equivalence relation on A (no induced K1+K2)
        ok = all(not (not adj(x, y) and not adj(y, z) and adj(x, z)) for x in A for y in A for z in A if len({x, y, z}) == 3)
        if not ok: continue
        if s_one and any(adj(x, y) for x, y in itertools.combinations(A, 2)): continue
        # B cluster: no induced P3
        if any(adj(x, y) and adj(y, z) and not adj(x, z) for x in B for y in B for z in B if len({x, y, z}) == 3): continue
        seen = set(); comps = 0
        for v in B:
            if v in seen: continue
            comps += 1; seen |= {w for w in B if w == v or adj(v, w)}
        if comps <= k: return True
    return False

counts = {n: len(conn[n]) + len(disc[n]) for n in range(1, N + 1)}
print('cograph counts', counts, flush=True)
# brute-force validation
checked = 0
for n in range(1, BRUTE + 1):
    for g in conn[n] + disc[n]:
        for k in range(0, 4):
            assert polar_inf(g, k) == brute(g, False, k), ('inf', show(g), k)
            assert polar_one(g, k) == brute(g, True, k), ('one', show(g), k)
            checked += 1
print('brute-force validated', checked, 'graph/k pairs up to order', BRUTE, flush=True)

census = {}
for k in range(0, KMAX + 1):
    obs = []
    for n in range(1, N + 1):
        for g in conn[n] + disc[n]:
            if polar_inf(g, k): continue
            if all(d is None or polar_inf(d, k) for d in deletions(g)):
                comps = components(g)
                c = len(comps); i = sum(1 for x in comps if x == V)
                obs.append((n, c, i, show(g), polar_one(g, k + 1)))
    bytype = {}
    for (n, c, i, s, p1) in obs:
        bytype.setdefault(f'({c},{i})', []).append({'order': n, 'graph': s, 'one_kplus1_polar': p1})
    census[k] = {'total_found': len(obs), 'max_order_found': max((o[0] for o in obs), default=None), 'by_type': bytype}
    conj = {t: len(v) for t, v in bytype.items() if 1 <= int(t[1:-1].split(',')[1]) <= int(t[1:-1].split(',')[0]) - 2 <= k}
    print(f'k={k}: obstructions found (order<={N}): {len(obs)}; max order {census[k]["max_order_found"]}; '
          f'conjecture-range type counts {dict(sorted(conj.items()))}', flush=True)
json.dump({'N': N, 'KMAX': KMAX, 'cograph_counts': counts, 'census': census}, open(OUT, 'w'), indent=1)
