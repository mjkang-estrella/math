"""Refined hypotheses on impure triangle configurations (triangle pairs non-PD + PB; X NOT assumed).
 H_mixed: if some minimal triangle fort Phi meets both A and B, then for p in Phi&A and x in S, {p,x} is non-PD.
 H_pureA: if a minimal triangle fort lies inside A, record whether some cross pair is non-PD anyway, and which.
usage: triangle_hyp.py s t chunk_bits chunk_index"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; Bmask = full = None
full = (1 << n) - 1; Bmask = full & ~Amask
bit = lambda c: sum(1 << v for v in c)
u, v, w = B[:3]; tri = [(u, v), (u, w), (v, w)]; S = B[3:]
PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
stats = {'graphs_impure': 0, 'has_mixed': 0, 'mixed_ok': 0, 'only_pureA': 0}; bad = []; pa = []
lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            a_, b_ = E[k]; adj[a_] |= 1 << b_; adj[b_] |= 1 << a_
    if any(a == 0 for a in adj): continue
    Fs = []; ok = True
    for e in tri:
        C = pdlib.closure(n, adj, bit(set(B) - set(e)))
        if C == full: ok = False; break
        Fs.append((e, full & ~C))
    if not ok: continue
    if not all(pdlib.is_pd(n, adj, X) for X in PBs): continue
    mixed = []; pureA = []
    for e, F in Fs:
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        for G in mins:
            if G & Amask and G & Bmask: mixed.append((e, G))
            elif G & Amask: pureA.append((e, G))
    if not mixed and not pureA: continue
    stats['graphs_impure'] += 1
    if mixed:
        stats['has_mixed'] += 1
        okm = all(not pdlib.is_pd(n, adj, (1 << p) | (1 << x)) for e, G in mixed for p in A if G >> p & 1 for x in S)
        if okm: stats['mixed_ok'] += 1
        elif len(bad) < 4: bad.append((pdlib.edges_of(n, adj), [(e, [z for z in range(n) if G >> z & 1]) for e, G in mixed]))
    else:
        stats['only_pureA'] += 1
        if len(pa) < 4: pa.append((pdlib.edges_of(n, adj), [(e, [z for z in range(n) if G >> z & 1]) for e, G in pureA],
                                   [(a, b) for a in A for b in B if not pdlib.is_pd(n, adj, (1 << a) | (1 << b))]))
print('s t chunk', s, t, cb, ci, stats, 'mixed-counter', bad, 'pureA-only examples', pa)
