"""Local form of the triangle lemma, with Z = cl(N[S]), S = B\\T, T = {u,v,w}:
 (a) cl(Z u N[a]) = V for all a in A;  (b) cl(Z u N[b] u N[b']) = V for distinct b,b' in T;
 (c) cl(Z u N[b]) != V for b in T.   (b),(c) are exactly PBT and the triangle; (a) is weaker than XS.
Report: graphs satisfying (a)(b)(c); impure count; and how many have A subset of Z (claim K1).
usage: triangle_local.py s t cb ci"""
import sys, itertools
sys.path.insert(0, 'scripts'); import pdlib
s, t, cb, ci = map(int, sys.argv[1:5]); n = s + t
E = list(itertools.combinations(range(n), 2)); m = len(E)
A = list(range(s)); B = list(range(s, n)); Amask = (1 << s) - 1; full = (1 << n) - 1
bit = lambda c: sum(1 << v for v in c)
T = B[:3]; S = B[3:]; Smask = bit(S)
tot = imp = k1 = 0; ex = []; exk1 = []; lo = m - cb
for low in range(1 << lo):
    mask = (ci << lo) | low
    adj = [0] * n
    for k in range(m):
        if mask >> k & 1:
            a_, b_ = E[k]; adj[a_] |= 1 << b_; adj[b_] |= 1 << a_
    if any(a == 0 for a in adj): continue
    Z = pdlib.closure(n, adj, Smask)
    # cl(Z u N[X]) computed as closure of the set Z u X (closure() adds N[X] for X; Z already closed so adding N[Z] is harmless? no) -> do it explicitly
    def clz(Y):
        O = Z | Y
        for y in range(n):
            if Y >> y & 1: O |= adj[y]
        return pdlib.closure(n, [0] * n, 0) if False else zf(O)
    def zf(O):
        ch = True
        while ch:
            ch = False
            for x in range(n):
                if O >> x & 1:
                    un = adj[x] & ~O
                    if un and un & (un - 1) == 0: O |= un; ch = True
        return O
    Cs = {b: clz(1 << b) for b in T}
    if any(Cs[b] == full for b in T): continue
    if any(clz((1 << b) | (1 << c)) != full for b, c in itertools.combinations(T, 2)): continue
    if any(clz(1 << a) != full for a in A): continue
    tot += 1
    if Amask & ~Z == 0: k1 += 1
    elif len(exk1) < 2: exk1.append(pdlib.edges_of(n, adj))
    bad = False
    for b in T:
        F = full & ~Cs[b]
        sub = [G for G in range(1, 1 << n) if G & ~F == 0 and pdlib.is_fort(n, adj, G)]
        mins = [G for G in sub if not any(H != G and H & G == H for H in sub)]
        if any(G & Amask for G in mins): bad = True
    if bad:
        imp += 1
        if len(ex) < 2: ex.append(pdlib.edges_of(n, adj))
print('s t chunk', s, t, cb, ci, 'graphs(a)(b)(c)', tot, 'impure', imp, 'A in Z', k1, 'impure examples', ex, 'A-not-in-Z examples', exk1)
