"""Graphs with triangle u,v,w (first 3 of B) pairs non-PD, PB holds, some minimal triangle-pair fort meets A.
For each, list impure A-vertices (in some minimal fort F with N[F] in A u e) and the non-PD cross pairs {a,b};
test the hypothesis: for every impure p and every x in S = B\\{u,v,w}, {p,x} is non-PD.
usage: triangle_witness.py s t chunk_bits chunk_index"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
u, v, w = B[:3]; tri = [(u, v), (u, w), (v, w)]; S = B[3:]
PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
tot = 0; hyp_ok = 0; hyp_bad = []; anyX = 0
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
        Fs.append(full & ~C)
    if not ok: continue
    if not all(pdlib.is_pd(n, adj, X) for X in PBs): continue
    impA = set()
    for F in Fs:
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        for G in mins:
            impA |= {a for a in A if G >> a & 1}
    if not impA: continue
    tot += 1
    nonX = [(a, b) for a in A for b in B if not pdlib.is_pd(n, adj, (1 << a) | (1 << b))]
    if nonX: anyX += 1
    h = all(not pdlib.is_pd(n, adj, (1 << p) | (1 << x)) for p in impA for x in S)
    if h: hyp_ok += 1
    elif len(hyp_bad) < 4: hyp_bad.append((pdlib.edges_of(n, adj), sorted(impA), nonX))
print('s t chunk', s, t, cb, ci, 'impure graphs', tot, 'with some nonPD cross pair', anyX, 'hyp {p,x} nonPD for all impure p, x in S:', hyp_ok, 'counter', hyp_bad)
