"""Exact checker for 365134 (Mkrtchyan, arXiv:2410.04389, Conjecture 8).

Multigraph G (loopless, cubic) as an edge list over vertices 0..n-1 (parallel edges allowed).
For a perfect matching F with complementary 2-factor Fbar, a non-conflicting nowhere-zero
Z2xZ2 flow of G/Fbar w.r.t. Fbar is equivalent to a labelling c: F -> {a,b,g} (g = a+b) with
  (flow)     for every cycle C of Fbar: sum over vertices u of C of c(F-edge at u) = 0,
             i.e. #a+#g even and #b+#g even on C (counting vertices; a loop of G/Fbar
             is an F-edge with both ends on C and is counted twice, contributing 0);
  (no conflict) no Fbar edge uv with {c(u), c(v)} = {a, b}.
"""
import itertools, sys, json

A, B, Gm = 1, 2, 3  # a=(1,0) b=(0,1) g=(1,1) encoded as bitmasks in Z2xZ2

def adjacency(n, E):
    inc = [[] for _ in range(n)]
    for k, (u, v) in enumerate(E):
        assert u != v
        inc[u].append(k); inc[v].append(k)
    assert all(len(x) == 3 for x in inc), 'not cubic'
    return inc

def perfect_matchings(n, E, inc):
    used = [False] * n; chosen = []
    def rec():
        try:
            u = used.index(False)
        except ValueError:
            yield list(chosen); return
        for k in inc[u]:
            a, b = E[k]; w = b if a == u else a
            if not used[w]:
                used[u] = used[w] = True; chosen.append(k)
                yield from rec()
                chosen.pop(); used[u] = used[w] = False
    yield from rec()

def cycles_of(n, E, inc, Fset):
    other = [[k for k in inc[u] if k not in Fset] for u in range(n)]
    seen = [False] * n; cyc = []
    for s in range(n):
        if seen[s]: continue
        C = [s]; seen[s] = True; prev = None; u = s; pk = None
        while True:
            ks = [k for k in other[u] if k != pk] if pk is not None else other[u][:1]
            if pk is not None and len(ks) == 0:  # digon: both Fbar edges parallel
                ks = [k for k in other[u] if k != pk]
            k = ks[0]; a, b = E[k]; w = b if a == u else a
            if w == s: break
            C.append(w); seen[w] = True; pk = k; u = w
        cyc.append(C)
    return cyc

def flow_exists(n, E, inc, F):
    Fset = set(F)
    mate = [None] * n; fid = [None] * n
    for i, k in enumerate(F):
        a, b = E[k]; mate[a] = b; mate[b] = a; fid[a] = fid[b] = i
    cyc = cycles_of(n, E, inc, Fset)
    if all(len(C) % 2 == 0 for C in cyc):
        return {'labels': {i: 'a' for i in range(len(F))}, 'cycles': cyc}
    # Fbar edges as pairs of F-indices
    fbar = [(fid[E[k][0]], fid[E[k][1]]) for k in range(len(E)) if k not in Fset]
    m = len(F)
    nbr = [[] for _ in range(m)]
    for x, y in fbar:
        if x != y: nbr[x].append(y); nbr[y].append(x)
    cyc_f = [[fid[u] for u in C] for C in cyc]
    in_cycles = [[] for _ in range(m)]
    for ci, C in enumerate(cyc_f):
        for x in C: in_cycles[x].append(ci)
    # order F-edges by cycles (BFS) for early parity checks
    order = []; placed = [False] * m
    for C in sorted(cyc_f, key=len):
        for x in C:
            if not placed[x]: placed[x] = True; order.append(x)
    last_pos = {}
    for ci, C in enumerate(cyc_f):
        last_pos[ci] = max(order.index(x) for x in C)
    closing = [[] for _ in range(m)]
    for ci in range(len(cyc_f)):
        closing[last_pos[ci]].append(ci)
    lab = [0] * m
    def ok_cycle(ci):
        s = 0
        for x in cyc_f[ci]: s ^= lab[x]
        return s == 0
    def rec(p):
        if p == m: return True
        x = order[p]
        for v in (Gm, A, B):
            bad = False
            for y in nbr[x]:
                if lab[y] and lab[y] != Gm and v != Gm and lab[y] != v:
                    bad = True; break
            if bad: continue
            lab[x] = v
            if all(ok_cycle(ci) for ci in closing[p]) and rec(p + 1):
                return True
            lab[x] = 0
        return False
    if rec(0):
        name = {A: 'a', B: 'b', Gm: 'g'}
        return {'labels': {i: name[lab[i]] for i in range(m)}, 'cycles': cyc}
    return None

def has_ham_path(n, E):
    adj = [0] * n
    for u, v in E: adj[u] |= 1 << v; adj[v] |= 1 << u
    full = (1 << n) - 1
    sys.setrecursionlimit(10000)
    from functools import lru_cache
    @lru_cache(None)
    def ext(mask, u):  # can we extend a path covering mask, ending at u, to cover all?
        if mask == full: return True
        r = adj[u] & ~mask
        while r:
            w = (r & -r).bit_length() - 1; r &= r - 1
            if ext(mask | 1 << w, w): return True
        return False
    for s in range(n):
        if ext(1 << s, s): return True
    return False

def bridgeless(n, E):
    for k in range(len(E)):
        adj = [[] for _ in range(n)]
        for j, (u, v) in enumerate(E):
            if j != k: adj[u].append(v); adj[v].append(u)
        seen = {0}; st = [0]
        while st:
            u = st.pop()
            for w in adj[u]:
                if w not in seen: seen.add(w); st.append(w)
        if len(seen) < n: return False
    return True

def three_edge_colourable(n, E, inc):
    for F in perfect_matchings(n, E, inc):
        cyc = cycles_of(n, E, inc, set(F))
        if all(len(C) % 2 == 0 for C in cyc): return True
    return False

def analyse(name, n, E, want_ham=True):
    inc = adjacency(n, E)
    res = {'name': name, 'n': n, 'bridgeless': bridgeless(n, E)}
    res['ham_path'] = has_ham_path(n, E) if want_ham else None
    npm = 0; witness = None
    for F in perfect_matchings(n, E, inc):
        npm += 1
        w = flow_exists(n, E, inc, F)
        if w is not None:
            witness = {'F': [E[k] for k in F], 'labels': w['labels'], 'cycles': w['cycles']}
            break
    res['pm_checked_until_witness'] = npm
    res['has_nc_flow'] = witness is not None
    res['witness'] = witness
    return res
