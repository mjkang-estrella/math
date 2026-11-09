"""MathDB 382049 (Mayhew-Probert Conjecture 4.2): list connected chordal graphs H on n vertices
(labelled, deduplicated by a canonical form) that are NOT isomorphic to C(G) for a chordal G, using
the source's printed Theorem 3.2 (Szwarcfiter-Bornstein): H = C(G) for connected chordal G iff H has a
spanning tree T such that for every edge uv of H the T-path from u to v induces a clique of H.
Usage: chordal_cliquegraph.py n"""
import sys, itertools
n = int(sys.argv[1])
E = list(itertools.combinations(range(n), 2))
def adj_of(mask):
    A = [0] * n
    for k, (i, j) in enumerate(E):
        if mask >> k & 1: A[i] |= 1 << j; A[j] |= 1 << i
    return A
def connected(A):
    seen = 1; st = [0]
    while st:
        v = st.pop(); nb = A[v] & ~seen
        seen |= nb
        st += [u for u in range(n) if nb >> u & 1]
    return seen == (1 << n) - 1
def chordal(A):  # repeatedly remove simplicial vertices
    alive = (1 << n) - 1
    while alive:
        for v in range(n):
            if alive >> v & 1:
                N = A[v] & alive
                if all((A[u] | (1 << u)) & N == N for u in range(n) if N >> u & 1):
                    alive &= ~(1 << v); break
        else:
            return False
    return True
def canon(A):
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((min(p[i], p[j]), max(p[i], p[j])) for i in range(n) for j in range(i + 1, n) if A[i] >> j & 1))
        if best is None or key < best: best = key
    return best
def is_clique(A, S):
    return all(A[u] >> v & 1 for u, v in itertools.combinations(S, 2))
def has_good_tree(A):
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i] >> j & 1]
    for T in itertools.combinations(edges, n - 1):
        par = list(range(n))
        def f(x):
            while par[x] != x: par[x] = par[par[x]]; x = par[x]
            return x
        ok = True
        for i, j in T:
            a, b = f(i), f(j)
            if a == b: ok = False; break
            par[a] = b
        if not ok: continue
        TA = [[] for _ in range(n)]
        for i, j in T: TA[i].append(j); TA[j].append(i)
        def path(u, v):
            prev = {u: None}; st = [u]
            while st:
                x = st.pop()
                for y in TA[x]:
                    if y not in prev: prev[y] = x; st.append(y)
            P = [v]
            while P[-1] != u: P.append(prev[P[-1]])
            return P
        if all(is_clique(A, path(u, v)) for u, v in edges):
            return True
    return False
seen = set(); bad = []; cnt = 0
for mask in range(1 << len(E)):
    A = adj_of(mask)
    if not connected(A) or not chordal(A): continue
    c = canon(A)
    if c in seen: continue
    seen.add(c); cnt += 1
    if not has_good_tree(A): bad.append(c)
print('n', n, 'connected chordal graphs up to iso', cnt, 'not C(chordal):', len(bad))
for c in bad: print('  edges', c)
