# Exhaustive check of Conjecture 3.1 of Bazzal-Togni (arXiv:2603.18674v1):
# every cubic Halin graph of order n>=6 is 2-tone 6-colorable.
# Cubic Halin graphs with l leaves <-> triangulations of a convex l-gon
# (tree = dual tree of the triangulation; leaves = polygon sides; the cycle
# joins consecutive sides). n = 2l-2. Classes up to dihedral symmetry.
# usage: halin2tone.py LMIN LMAX [K]
import sys, itertools
from functools import lru_cache

def triangulations(vs):
    # vs: tuple of polygon vertex labels in order; yield frozensets of triangles
    if len(vs) < 3:
        yield ()
        return
    a, b = vs[0], vs[-1]
    for i in range(1, len(vs) - 1):
        c = vs[i]
        for left in triangulations(vs[:i + 1]):
            for right in triangulations(vs[i:]):
                yield ((a, c, b),) + left + right

def canon(tris, l):
    best = None
    for r in range(l):
        for s in (1, -1):
            img = tuple(sorted(tuple(sorted(((s * x + r) % l) for x in t)) for t in tris))
            if best is None or img < best:
                best = img
    return best

def halin(tris, l):
    # vertices: triangles 0..T-1, then leaves T..T+l-1 (leaf j = side (j,j+1))
    T = len(tris)
    n = T + l
    adj = [set() for _ in range(n)]
    side_owner = {}
    for ti, t in enumerate(tris):
        for e in itertools.combinations(sorted(t), 2):
            side_owner.setdefault(e, []).append(ti)
    for e, ts in side_owner.items():
        x, y = e
        if (y - x) % l == 1 or (x - y) % l == 1:
            j = x if (y - x) % l == 1 else y
            assert len(ts) == 1
            u, v = ts[0], T + j
            adj[u].add(v); adj[v].add(u)
        else:
            assert len(ts) == 2
            u, v = ts
            adj[u].add(v); adj[v].add(u)
    for j in range(l):
        u, v = T + j, T + (j + 1) % l
        adj[u].add(v); adj[v].add(u)
    assert all(len(a) == 3 for a in adj), [len(a) for a in adj]
    return [sorted(a) for a in adj]

def colorable(adj, K):
    n = len(adj)
    labels = list(itertools.combinations(range(K), 2))
    L = len(labels)
    full = (1 << L) - 1
    adjconf = [0] * L  # labels that may NOT be on a neighbour
    for i, a in enumerate(labels):
        for j, b in enumerate(labels):
            if set(a) & set(b):
                adjconf[i] |= 1 << j
    d2 = [set() for _ in range(n)]
    for v in range(n):
        for u in adj[v]:
            for w in adj[u]:
                if w != v and w not in adj[v]:
                    d2[v].add(w)
    d2 = [sorted(s) for s in d2]
    dom = [full] * n
    col = [-1] * n
    # symmetry: find a triangle and fix its labels to {01},{23},{45} (needs K=6 partition) ;
    # generic fallback: fix the first vertex label only.
    tri = None
    for v in range(n):
        for u in adj[v]:
            for w in adj[u]:
                if w in adj[v] and u < w:
                    tri = (v, u, w); break
            if tri: break
        if tri: break
    order_fixed = []
    if tri and K == 6:
        order_fixed = [(tri[0], labels.index((0, 1))), (tri[1], labels.index((2, 3))), (tri[2], labels.index((4, 5)))]
    else:
        order_fixed = [(0, 0)]
    nodes = [0]

    def assign(v, c, dom):
        nd = dom[:]
        nd[v] = 1 << c
        for u in adj[v]:
            nd[u] &= ~adjconf[c]
            if nd[u] == 0 and col[u] == -1:
                return None
            if col[u] != -1 and not (nd[u] >> col[u]) & 1:
                return None
        for u in d2[v]:
            nd[u] &= ~(1 << c)
            if col[u] != -1 and not (nd[u] >> col[u]) & 1:
                return None
            if nd[u] == 0:
                return None
        return nd

    for v, c in order_fixed:
        if not (dom[v] >> c) & 1:
            return None
        dom = assign(v, c, dom)
        if dom is None:
            return None
        col[v] = c

    def rec(dom):
        nodes[0] += 1
        best = -1; bc = 99
        for v in range(n):
            if col[v] == -1:
                c = bin(dom[v]).count('1')
                if c < bc:
                    bc = c; best = v
                    if c <= 1: break
        if best == -1:
            return True
        v = best
        m = dom[v]
        while m:
            c = (m & -m).bit_length() - 1
            m &= m - 1
            nd = assign(v, c, dom)
            if nd is not None:
                col[v] = c
                if rec(nd):
                    return True
                col[v] = -1
        return False

    ok = rec(dom)
    return ([labels[c] for c in col] if ok else False), nodes[0]

def verify(adj, colr):
    n = len(adj)
    for v in range(n):
        for u in adj[v]:
            if set(colr[v]) & set(colr[u]): return False
        for u in adj[v]:
            for w in adj[u]:
                if w != v and w not in adj[v] and colr[w] == colr[v]: return False
    return True

def triangulations_apex(l, lo, hi):
    # top-level split: triangle on side (0, l-1) with apex i in [lo, hi)
    vs = tuple(range(l)); a, b = vs[0], vs[-1]
    for i in range(max(1, lo), min(hi, l - 1)):
        c = vs[i]
        for left in triangulations(vs[:i + 1]):
            for right in triangulations(vs[i:]):
                yield ((a, c, b),) + left + right

if __name__ == '__main__' and sys.argv[1] == 'chunk':
    # every triangulation is tested directly (no cross-chunk dedupe); chunks partition all triangulations
    l, lo, hi = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    seen = set(); bad = []; tested = 0; total = 0; maxnodes = 0
    for tris in triangulations_apex(l, lo, hi):
        total += 1
        c = canon(tris, l)
        if c in seen: continue
        seen.add(c); tested += 1
        adj = halin(list(c), l)
        res, nodes = colorable(adj, 6)
        maxnodes = max(maxnodes, nodes)
        if res is False: bad.append(c)
        else: assert verify(adj, res)
    print(f'l={l} n={2*l-2} apex [{lo},{hi}) triangulations={total} distinct-in-chunk={tested} non-colorable={len(bad)} maxnodes={maxnodes}')
    for b in bad[:5]: print('  BAD', b)
    sys.exit(0)

if __name__ == '__main__':
    lmin, lmax = int(sys.argv[1]), int(sys.argv[2])
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    for l in range(lmin, lmax + 1):
        seen = set(); bad = []; maxnodes = 0; total = 0
        for tris in triangulations(tuple(range(l))):
            total += 1
            c = canon(tris, l)
            if c in seen: continue
            seen.add(c)
            adj = halin(list(c), l)
            res, nodes = colorable(adj, K)
            maxnodes = max(maxnodes, nodes)
            if res is False:
                bad.append(c)
            else:
                assert verify(adj, res)
        print(f'l={l} n={2*l-2} triangulations={total} classes={len(seen)} K={K} non-colorable={len(bad)} maxnodes={maxnodes}', flush=True)
        for b in bad[:5]:
            print('  BAD', b, flush=True)
