"""Print sample impure triangle configurations (X assumed only for display of failure): forts per triangle pair,
the mixed fort, and the maximal fort avoiding N[S u {p}].  usage: triangle_show.py s t chunk_bits chunk_index maxshow"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci, mx = map(int, sys.argv[1:6]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1; Bmask = full & ~Amask
bit = lambda c: sum(1 << v for v in c); L = lambda G: [z for z in range(n) if G >> z & 1]
u, v, w = B[:3]; tri = [(u, v), (u, w), (v, w)]; S = B[3:]
PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
shown = 0; lo = m - cb
import random
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
    rows = []; mixedA = set()
    for e, F in Fs:
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        rows.append((e, L(F), [L(G) for G in mins]))
        for G in mins:
            if G & Amask and G & Bmask: mixedA |= {p for p in A if G >> p & 1}
    if not mixedA: continue
    if low % 7: continue
    print('edges', pdlib.edges_of(n, adj))
    print('  nbrs', {z: L(adj[z]) for z in range(n)})
    for r in rows: print('  pair', r[0], 'maxfort', r[1], 'minforts', r[2])
    for p in sorted(mixedA):
        Cp = pdlib.closure(n, adj, bit(S) | (1 << p))
        print('  p', p, 'cl(N[S+p])', L(Cp), 'maxfort avoiding', L(full & ~Cp))
    shown += 1
    if shown >= mx: break
