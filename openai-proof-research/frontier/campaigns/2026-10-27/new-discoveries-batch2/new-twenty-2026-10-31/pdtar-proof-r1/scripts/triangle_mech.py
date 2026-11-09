"""Mechanism probe (H2 = PBT, H3 = triangle non-PD hold; H1 = {a,x} PD may fail).
For graphs with an A-vertex p in some maximal triangle fort M_b = V \\ cl(N[S u {b}]) (b in T):
 Q1: is cl(N[S u {p}]) != V (H1 fails at p)?   [expected yes if claim M is the right lemma]
 Q2: is U \\ N[p] (U = union of the three maximal forts) a fort?  Q3: is the maximal fort avoiding N[S u {p}] inside U?
 Q4: membership pattern of p in (M_u, M_v, M_w) and adjacency of p to (u,v,w).
usage: triangle_mech.py s t cb ci"""
import sys, itertools
from collections import Counter
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
T = B[:3]; S = B[3:]; Smask = bit(S)
c = Counter(); bad = []; lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            a_, b_ = E[k]; adj[a_] |= 1 << b_; adj[b_] |= 1 << a_
    if any(a == 0 for a in adj): continue
    M = {b: full & ~pdlib.closure(n, adj, Smask | (1 << b)) for b in T}
    if any(M[b] == 0 for b in T): continue
    if any(pdlib.is_pd(n, adj, Smask | (1 << b) | (1 << b2)) == False for b, b2 in itertools.combinations(T, 2)): continue
    U = M[T[0]] | M[T[1]] | M[T[2]]
    for p in A:
        if not any(M[b] >> p & 1 for b in T): continue
        Cp = pdlib.closure(n, adj, Smask | (1 << p))
        q1 = Cp != full
        Np = adj[p] | (1 << p)
        q2 = pdlib.is_fort(n, adj, U & ~Np)
        q3 = (full & ~Cp) & ~U == 0
        pat = (tuple(int(M[b] >> p & 1) for b in T), tuple(int(adj[p] >> b & 1) for b in T))
        c[(q1, q2, q3, pat)] += 1
        if not q1 and len(bad) < 3: bad.append(pdlib.edges_of(n, adj))
print('s t chunk', s, t, cb, ci)
for k, v in sorted(c.items()): print('Q1', k[0], 'Q2', k[1], 'Q3', k[2], 'in(Mu,Mv,Mw)', k[3][0], 'adj(u,v,w)', k[3][1], 'count', v)
print('Q1 failures', bad)
