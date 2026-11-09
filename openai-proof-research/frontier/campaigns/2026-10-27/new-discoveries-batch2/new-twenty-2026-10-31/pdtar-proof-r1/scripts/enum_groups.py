"""Exhaustive enumeration over all graphs on A u B (|A|=s,|B|=t), chunked by the top edge bits.
For each graph record which constraint groups of 'same PD family as K_{s,t}' hold:
 X = every cross pair {a,b} PD; PA = every (s-1)-subset of A PD; PB = same for B;
 NA = every (s-2)-subset of A non-PD; NB = same for B.  (no-isolated is implied by PA&PB&NA... recorded too)
Prints counts for each pattern that misses at most one group, plus examples.
usage: enum_groups.py s t chunk_bits chunk_index"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n))
bit = lambda c: sum(1 << v for v in c)
cross = [(1 << a) | (1 << b) for a in A for b in B]
PAs = [bit(c) for c in itertools.combinations(A, s - 1)]; PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
NAs = [bit(c) for c in itertools.combinations(A, s - 2)]; NBs = [bit(c) for c in itertools.combinations(B, t - 2)]
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
    groups = []
    g = {}
    g['X'] = all(pdlib.is_pd(n, adj, S) for S in cross)
    g['NA'] = not any(pdlib.is_pd(n, adj, S) for S in NAs)
    g['NB'] = not any(pdlib.is_pd(n, adj, S) for S in NBs)
    miss = [k for k in ('X', 'NA', 'NB') if not g[k]]
    if len(miss) > 1: continue
    g['PA'] = all(pdlib.is_pd(n, adj, S) for S in PAs)
    g['PB'] = all(pdlib.is_pd(n, adj, S) for S in PBs)
    miss = tuple(k for k in ('X', 'PA', 'PB', 'NA', 'NB') if not g[k])
    if len(miss) > 1: continue
    cnt[miss] += 1
    if len(ex.setdefault(miss, [])) < 3: ex[miss].append(pdlib.edges_of(n, adj))
print('s t chunk', s, t, cb, ci)
for k, v in sorted(cnt.items()): print('missing', k, 'count', v, 'examples', ex[k])
