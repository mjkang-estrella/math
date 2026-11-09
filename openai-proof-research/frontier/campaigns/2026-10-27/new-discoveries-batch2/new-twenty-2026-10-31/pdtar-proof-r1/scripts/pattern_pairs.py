"""All graphs on A u B satisfying C1 (cross pairs, (s-1)-subsets of A, (t-1)-subsets of B are PD).
Record the set of non-PD B-pairs (as a graph on B, canonicalised under Sym(B)) and of non-PD A-pairs complements,
split by whether some minimal fort avoiding N[B\\e] meets A.  usage: pattern_pairs.py s t chunk_bits chunk_index"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
cross = [(1 << a) | (1 << b) for a in A for b in B]
PAs = [bit(c) for c in itertools.combinations(A, s - 1)]; PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
pairsB = list(itertools.combinations(B, 2))
perms = list(itertools.permutations(B))
def canon(es):
    best = None
    for p in perms:
        mp = dict(zip(B, p)); c = tuple(sorted(tuple(sorted((mp[u], mp[v]))) for u, v in es))
        if best is None or c < best: best = c
    return best
from collections import Counter
cnt = Counter()
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
    nonpd = []; imp = False
    for (u, v) in pairsB:
        C = pdlib.closure(n, adj, bit(set(B) - {u, v}))
        if C != full:
            nonpd.append((u, v)); F = full & ~C
            sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
            mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
            if any(G & Amask for G in mins): imp = True
    cnt[(imp, canon(nonpd))] += 1
print('s t chunk', s, t, cb, ci)
for k, v in sorted(cnt.items()): print('impure' if k[0] else 'pure  ', 'nonPD-pairs', k[1], 'count', v)
