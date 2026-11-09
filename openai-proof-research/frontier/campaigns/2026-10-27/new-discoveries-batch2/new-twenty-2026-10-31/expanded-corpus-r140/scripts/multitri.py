"""Exhaustive check of Conjecture 3.8 (MathDB 368931) of Solotko-Tung-Yang-Zhang,
arXiv:2506.16598v2, for small k and n.

Model (source Section 2): vertices of the universal cover are the integers.
An edge [a,b] (a<b) has length b-a.  Edges [a1,b1],[a2,b2] intersect iff
a1<a2<b1<b2 (or symmetric).  A (k+1)-crossing is k+1 pairwise intersecting
edges.  A k-triangulation T on C_n is a maximal set of edge classes (edges of
C_n = edges of the cover modulo translation by n) whose lift is
(k+1)-crossing-free.  Edges of length <= k never occur in a (k+1)-crossing, so
they are always present; by Convention 2.3 edges of length < k are excluded,
edges of length k (k-boundary edges) are kept.  Lemma 3.1: no edge of length
> kn.  So T is determined by its set of classes (r mod n, l), k<l<=kn.

Angle (Def 2.6): edges [u,v],[v,w] in the lift, u < v < w in the cyclic order
(Z plus a point at infinity), with no edge [v,w0], w < w0 < u cyclically.
k-relevant angle: at least one of the two edges has length in (k, kn).
k-star: z0<...<z_{2k} with all edges [z_i, z_{i+k}] (indices mod 2k+1).
Angle (u,v,w) belongs to the star iff v=z_i, w=z_{i+k}, u=z_{i+k+1}.
"""
import sys, itertools, json

def classes(n, k):
    return [(r, l) for l in range(k + 1, k * n + 1) for r in range(n)]

def lift(S, n, lo, hi):
    """all lifted edges (a,b) with lo<=a<hi for classes S (set of (r,l))"""
    out = []
    for (r, l) in S:
        a0 = lo + ((r - lo) % n)
        for a in range(a0, hi, n):
            out.append((a, a + l))
    return out

def has_crossing(S, n, k):
    """(k+1)-crossing in the lift of S (relevant classes only)."""
    if not S:
        return False
    L = max(l for _, l in S)
    edges = lift(S, n, 0, n + L)
    edges.sort()
    for (a1, b1) in edges:
        if a1 >= n:
            break
        cand = [(a, b) for (a, b) in edges if a1 < a < b1 and b > b1]
        # longest chain strictly increasing in a and b
        cand.sort()
        best = {}
        m = 0
        for i, (a, b) in enumerate(cand):
            v = 1
            for j in range(i):
                aj, bj = cand[j]
                if aj < a and bj < b and best[j] + 1 > v:
                    v = best[j] + 1
            best[i] = v
            if v > m:
                m = v
        if m >= k:
            return True
    return False

def enumerate_tri(n, k):
    C = classes(n, k)
    res = []
    def rec(i, S):
        if i == len(C):
            # maximality
            for c in C:
                if c not in S and not has_crossing(S | {c}, n, k):
                    return
            res.append(frozenset(S))
            return
        c = C[i]
        S2 = S | {c}
        if not has_crossing(S2, n, k):
            rec(i + 1, S2)
        # exclude c: only useful if c will be blocked eventually; prune lazily
        rec(i + 1, S)
    rec(0, frozenset())
    return res

def check(T, n, k):
    """return list of k-relevant angles (at v in [0,n)) not in exactly one star"""
    full = set(T) | {(r, k) for r in range(n)}
    W = 4 * k * n + 4
    E = set(lift(full, n, -W, W))
    adj = {}
    for (a, b) in E:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    BIG = 10 ** 6
    bad = []
    stats = {'angles': 0, 'relevant': 0}
    for v in range(n):
        key = lambda x: (x - v) if x > v else (x - v + BIG)
        nb = sorted(adj[v], key=key)
        for idx in range(len(nb) - 1):
            w, u = nb[idx], nb[idx + 1]
            stats['angles'] += 1
            luv, lvw = abs(u - v), abs(w - v)
            if not ((k < luv < k * n) or (k < lvw < k * n)):
                continue
            stats['relevant'] += 1
            # search stars: y0=v, y_k=w, y_{k+1}=u, cyclic order from v
            kw, ku = key(w), key(u)
            pts = [x for x in range(v - 2 * k * n - 2, v + 2 * k * n + 3) if x != v]
            inner1 = sorted([x for x in pts if 0 < key(x) < kw], key=key)
            inner2 = sorted([x for x in pts if key(x) > ku], key=key)
            count = 0
            stars = []
            for A in itertools.combinations(inner1, k - 1):
                for B in itertools.combinations(inner2, k - 1):
                    y = [v] + list(A) + [w, u] + list(B)
                    ok = True
                    for j in range(2 * k + 1):
                        a, b = y[j], y[(j + k) % (2 * k + 1)]
                        if (min(a, b), max(a, b)) not in E:
                            ok = False
                            break
                    if ok:
                        count += 1
                        stars.append(y)
            if count != 1:
                bad.append({'v': v, 'w': w, 'u': u, 'count': count, 'stars': stars[:3]})
    return bad, stats

if __name__ == '__main__':
    k = int(sys.argv[1]); nmax = int(sys.argv[2])
    for n in range(1, nmax + 1):
        Ts = enumerate_tri(n, k)
        nbad = 0
        sizes = set()
        ex = None
        tot = {'angles': 0, 'relevant': 0}
        for T in Ts:
            bad, st = check(T, n, k)
            for x in tot: tot[x] += st[x]
            sizes.add(len(T))
            if bad:
                nbad += 1
                if ex is None:
                    ex = {'T': sorted(T), 'bad': bad[:4]}
        print(json.dumps({'k': k, 'n': n, 'num_triangulations': len(Ts), 'relevant_edge_counts': sorted(sizes),
                          'num_failing': nbad, 'angle_stats': tot, 'example': ex}), flush=True)
