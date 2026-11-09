"""Exact small-case check of the Huang-Zhang-Chen conjecture (MathDB 376132):
R(T_n, C_m) = 2n-1 for odd m >= 5, n >= ceil((2m-1)/3).
The lower bound 2n-1 is classical (two red K_{n-1}).  For the upper bound we
must show: every red graph R on N = 2n-1 vertices contains T_n or its
complement contains C_m.  Both 'R is T-free' and 'complement(R) is C_m-free'
are hereditary (closed under induced subgraphs), so we build, vertex by vertex,
all graphs (up to isomorphism) on j vertices with both properties; the
conjecture holds for (T, m) iff this family is empty at j = N.
Usage: treecycle.py m n   (all trees on n vertices)
"""
import sys, json, itertools
from functools import lru_cache

def trees(n):
    """all unlabeled trees on n vertices: leaf extension + canonical AHU encoding"""
    level = {tree_canon(1, []): (1, [])}
    for k in range(1, n):
        nxt = {}
        for (kk, E) in level.values():
            for v in range(kk):
                E2 = E + [(v, kk)]
                c = tree_canon(kk + 1, E2)
                if c not in nxt: nxt[c] = (kk + 1, E2)
        level = nxt
    return [E for (_, E) in level.values()]

def tree_canon(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges: adj[a].append(b); adj[b].append(a)
    if n == 1: return '()'
    def enc(v, p):
        return '(' + ''.join(sorted(enc(w, v) for w in adj[v] if w != p)) + ')'
    return min(enc(r, -1) for r in range(n))

def contains_tree(adjm, N, T, n):
    """adjm: list of int bitmasks. T: edge list on n vertices. subgraph (not induced) embedding"""
    tadj = [[] for _ in range(n)]
    for a, b in T: tadj[a].append(b); tadj[b].append(a)
    # BFS order from a max-degree root, parent of each
    root = max(range(n), key=lambda v: len(tadj[v]))
    order = [root]; par = {root: -1}
    for v in order:
        for w in tadj[v]:
            if w not in par: par[w] = v; order.append(w)
    tdeg = [len(tadj[v]) for v in range(n)]
    gdeg = [bin(adjm[v]).count('1') for v in range(N)]
    img = [0] * n
    def dfs(i, used):
        if i == n: return True
        v = order[i]
        if i == 0:
            cand = (1 << N) - 1
        else:
            cand = adjm[img[par[v]]] & ~used
        while cand:
            low = cand & -cand; x = low.bit_length() - 1; cand ^= low
            if gdeg[x] < tdeg[v]: continue
            img[v] = x
            if dfs(i + 1, used | low): return True
        return False
    return dfs(0, 0)

def contains_cycle(adjm, N, m):
    """cycle of length exactly m in graph given by bitmasks"""
    for s in range(N):
        # cycles whose minimum vertex is s
        allowed = sum(1 << x for x in range(s + 1, N))
        def dfs(v, used, length):
            if length == m:
                return (adjm[v] >> s) & 1
            cand = adjm[v] & allowed & ~used
            while cand:
                low = cand & -cand; x = low.bit_length() - 1; cand ^= low
                if dfs(x, used | low, length + 1): return True
            return False
        if dfs(s, 1 << s, 1): return True
    return False

def refine(adjm, N):
    col = [bin(a).count('1') for a in adjm]
    for _ in range(N):
        sig = [(col[v], tuple(sorted(col[w] for w in range(N) if adjm[v] >> w & 1))) for v in range(N)]
        keys = sorted(set(sig)); new = [keys.index(x) for x in sig]
        if len(set(new)) == len(set(col)):
            col = new; break
        col = new
    # invariant: sorted signature list (uses final colours only through structure)
    inv = tuple(sorted(sig))
    return col, inv

def isomorphic(A, ca, B, cb, N):
    """exact iso test respecting refined colours (colours are canonical class indices)"""
    if sorted(ca) != sorted(cb): return False
    order = sorted(range(N), key=lambda v: (sum(1 for w in range(N) if ca[w] == ca[v]), v))
    mp = [-1] * N; used = 0
    def dfs(i, used):
        if i == N: return True
        v = order[i]
        for x in range(N):
            if used >> x & 1 or cb[x] != ca[v]: continue
            ok = True
            for j in range(i):
                u = order[j]
                if ((A[v] >> u) & 1) != ((B[x] >> mp[u]) & 1): ok = False; break
            if ok:
                mp[v] = x
                if dfs(i + 1, used | (1 << x)): return True
                mp[v] = -1
        return False
    return dfs(0, 0)

def add_noniso(store, a, N):
    col, inv = refine(a, N)
    bucket = store.setdefault(inv, [])
    for (b, cb) in bucket:
        if isomorphic(a, col, b, cb, N): return False
    bucket.append((a, col)); return True

def cycle_through(adjm, N, m, v):
    """cycle of length m through vertex v (graph otherwise assumed C_m-free)"""
    nb = adjm[v]
    def dfs(x, used, length, start):
        if length == m:
            return (adjm[x] >> v) & 1 and x != start
        cand = adjm[x] & ~used
        while cand:
            low = cand & -cand; y = low.bit_length() - 1; cand ^= low
            if dfs(y, used | low, length + 1, start): return True
        return False
    c = nb
    while c:
        low = c & -c; s0 = low.bit_length() - 1; c ^= low
        if dfs(s0, (1 << v) | low, 2, s0): return True
    return False

def run(m, n, T):
    N = 2 * n - 1
    fam = [[0]]
    sizes = [1]
    for j in range(1, N):
        store = {}; cnt = 0; nxt = []
        for adjm in fam:
            for S in range(1 << j):
                a = list(adjm) + [S]
                for x in range(j):
                    if S >> x & 1: a[x] |= 1 << j
                comp = [((~a[v]) & ((1 << (j + 1)) - 1)) & ~(1 << v) for v in range(j + 1)]
                if cycle_through(comp, j + 1, m, j): continue
                if contains_tree(a, j + 1, T, n): continue
                if add_noniso(store, a, j + 1): nxt.append(a)
        fam = nxt
        sizes.append(len(fam))
        if not fam: break
    return sizes, (fam[0] if fam else None)

if __name__ == '__main__':
    m, n = int(sys.argv[1]), int(sys.argv[2])
    Ts = trees(n)
    lo, hi = (int(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (0, len(Ts))
    for i in range(lo, min(hi, len(Ts))):
        T = Ts[i]
        sizes, ex = run(m, n, T)
        print(json.dumps({'m': m, 'n': n, 'tree_index': i, 'num_trees': len(Ts), 'tree': T, 'family_sizes_by_order': sizes, 'N': 2 * n - 1, 'counterexample': ex}), flush=True)
