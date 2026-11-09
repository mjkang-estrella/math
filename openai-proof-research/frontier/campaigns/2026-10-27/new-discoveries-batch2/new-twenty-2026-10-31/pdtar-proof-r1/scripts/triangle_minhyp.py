"""Minimal-hypothesis test for the triangle lemma.  Hypotheses (always): no isolated vertex, triangle pairs of
T={u,v,w} non-PD (B\\e non-PD), plus chosen subset of:
  XS  : {a,x} PD for all a in A, x in S=B\\T
  XT  : {a,b} PD for all a in A, b in T
  PB  : B\\{b} PD for all b in B
  PBT : B\\{b} PD for b in T only
Report count of graphs and count with an impure triangle fort.  usage: triangle_minhyp.py s t groups cb ci"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t = int(sys.argv[1]), int(sys.argv[2]); groups = set(sys.argv[3].split(',')) - {''}
cb, ci = int(sys.argv[4]), int(sys.argv[5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
T = B[:3]; u, v, w = T; tri = [(u, v), (u, w), (v, w)]; S = B[3:]
chk = []
if 'XS' in groups: chk += [(1 << a) | (1 << x) for a in A for x in S]
if 'XT' in groups: chk += [(1 << a) | (1 << b) for a in A for b in T]
if 'PB' in groups: chk += [bit(set(B) - {b}) for b in B]
elif 'PBT' in groups: chk += [bit(set(B) - {b}) for b in T]
tot = imp = 0; ex = []; lo = m - cb
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
    if not all(pdlib.is_pd(n, adj, X) for X in chk): continue
    tot += 1
    bad = False
    for F in Fs:
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        if any(G & Amask for G in mins): bad = True
    if bad:
        imp += 1
        if len(ex) < 2: ex.append(pdlib.edges_of(n, adj))
print('s t groups chunk', s, t, sorted(groups), cb, ci, 'graphs', tot, 'impure', imp, 'examples', ex)
