# variant of lemmaG.py with F3 (N[a] meets every M_b) as extra hypothesis
"""Lemma G test. Hypotheses: no isolated vertex, H2 (cl(N[S u {b,b'}]) = V for distinct b,b' in T), H3 (M_b != empty).
For every p in A, w in T with p in M_w, and v in T\\{w} with p not adjacent to v:
 check G = (M_w u M_v) \\ N[p] is a nonempty fort.  usage: lemmaG.py s t cb ci"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
T = B[:3]; S = B[3:]; Smask = bit(S)
tested = good = 0; bad = []; lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            a_, b_ = E[k]; adj[a_] |= 1 << b_; adj[b_] |= 1 << a_
    if any(a == 0 for a in adj): continue
    M = {b: full & ~pdlib.closure(n, adj, Smask | (1 << b)) for b in T}
    if any(M[b] == 0 for b in T): continue
    if not all(pdlib.is_pd(n, adj, Smask | (1 << b) | (1 << b2)) for b, b2 in itertools.combinations(T, 2)): continue
    if not all(M[b] & (adj[a] | (1 << a)) for b in T for a in A): continue  # F3
    for p in A:
        for w in T:
            if not M[w] >> p & 1: continue
            for v in T:
                if v == w or adj[p] >> v & 1: continue
                tested += 1
                G = (M[w] | M[v]) & ~(adj[p] | (1 << p))
                if pdlib.is_fort(n, adj, G): good += 1
                elif len(bad) < 4: bad.append((pdlib.edges_of(n, adj), 'p', p, 'w', w, 'v', v, 'Mw', M[w], 'Mv', M[v]))
print('s t chunk', s, t, cb, ci, 'tested', tested, 'fort', good, 'bad', bad)
