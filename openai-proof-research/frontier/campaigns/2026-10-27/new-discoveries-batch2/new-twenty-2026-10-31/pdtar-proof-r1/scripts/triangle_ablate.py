"""Triangle lemma ablation: graphs on A u B (no isolated vertices) where B\\{u,v}, B\\{u,w}, B\\{v,w} are non-PD
for the fixed triangle u,v,w = first three B vertices; with a chosen subset of the C1 groups (X, PA, PB).
Count graphs where some minimal fort avoiding N[B\\e] (e a triangle pair) meets A ('impure').
usage: triangle_ablate.py s t groups chunk_bits chunk_index   (groups e.g. X,PA,PB)"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t = int(sys.argv[1]), int(sys.argv[2]); groups = set(sys.argv[3].split(',')) - {''}
cb, ci = int(sys.argv[4]), int(sys.argv[5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
u, v, w = B[:3]; tri = [(u, v), (u, w), (v, w)]
cross = [(1 << a) | (1 << b) for a in A for b in B]
PAs = [bit(c) for c in itertools.combinations(A, s - 1)]; PBs = [bit(c) for c in itertools.combinations(B, t - 1)]
tot = imp = 0; ex = []
lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            a_, b_ = E[k]; adj[a_] |= 1 << b_; adj[b_] |= 1 << a_
    if any(a == 0 for a in adj): continue
    Fs = []
    ok = True
    for e in tri:
        C = pdlib.closure(n, adj, bit(set(B) - set(e)))
        if C == full: ok = False; break
        Fs.append(full & ~C)
    if not ok: continue
    if 'X' in groups and not all(pdlib.is_pd(n, adj, S) for S in cross): continue
    if 'PA' in groups and not all(pdlib.is_pd(n, adj, S) for S in PAs): continue
    if 'PB' in groups and not all(pdlib.is_pd(n, adj, S) for S in PBs): continue
    tot += 1
    bad = False
    for F in Fs:
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        if any(G & Amask for G in mins): bad = True
    if bad:
        imp += 1
        if len(ex) < 3: ex.append(pdlib.edges_of(n, adj))
print('s t groups chunk', s, t, sorted(groups), cb, ci, 'graphs', tot, 'impure', imp, 'examples', ex)
