"""Among all graphs on A u B (s,t) with no isolated vertex satisfying X (cross pairs PD), PA, PB:
for each pair {u,v} in B with B\\{u,v} non-PD, check whether some minimal fort F with N[F] subset of A u {u,v} meets A ('impure').
Report graphs having an impure pair-fort, and which pairs of B have B\\{u,v} PD (i.e. NB fails)."""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1
bit = lambda c: sum(1 << v for v in c)
cross = [(1 << a) | (1 << b) for a in A for b in B]
PAs = [bit(c) for c in itertools.combinations(A, s - 1)]; PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
pairsB = list(itertools.combinations(B, 2))
from collections import Counter
cnt = Counter(); ex = {}
lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            u, v = E[k]; adj[u] |= 1 << v; adj[v] |= 1 << u
    if any(a == 0 for a in adj): continue
    if not all(pdlib.is_pd(n, adj, S) for S in cross): continue
    if not all(pdlib.is_pd(n, adj, S) for S in PAs): continue
    if not all(pdlib.is_pd(n, adj, S) for S in PBs): continue
    full = (1 << n) - 1
    nonpd_pairs = []; impure = []
    for (u, v) in pairsB:
        S = bit(set(B) - {u, v})
        C = pdlib.closure(n, adj, S)
        if C != full:
            nonpd_pairs.append((u, v))
            F = full & ~C  # maximal fort avoiding N[S]
            # minimal forts inside F
            sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
            mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
            if any(G & Amask for G in mins): impure.append(((u, v), [[w for w in range(n) if G >> w & 1] for G in mins]))
    if impure:
        key = (len(nonpd_pairs), len(impure))
        cnt[key] += 1
        if len(ex.setdefault(key, [])) < 2: ex[key].append((pdlib.edges_of(n, adj), 'nonPDpairs', nonpd_pairs, 'impure', impure))
print('s t chunk', s, t, cb, ci, 'total pairs', len(pairsB))
for k, v in sorted(cnt.items()): print('(#nonPD pairs, #impure)', k, 'count', v); [print('   ', e) for e in ex[k]]
