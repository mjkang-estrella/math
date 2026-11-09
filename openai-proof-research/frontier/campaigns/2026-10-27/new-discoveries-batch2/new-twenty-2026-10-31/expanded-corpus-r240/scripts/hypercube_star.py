"""348106: can m = ceil(n/2)-1 vertex-disjoint sub-stars (stars with <= r = n leaves, i.e. a centre plus
some of its neighbours) disconnect Q_n?  Reduction: if some choice R of such stars disconnects Q_n, then
with U = union of the closed balls B[c_i] around the centres either (1) Q_n - U is disconnected, or
(2) some non-centre u in U has N(u) contained in U (then R' = U - {u} works). Conversely each of (1),(2)
yields a disconnecting family of disjoint sub-stars (assign each vertex of U to an adjacent centre).
Exhaustive over centre tuples with c1 = 0 and c2 a weight representative (vertex- and coordinate-
symmetry), remaining centres arbitrary distinct.  Usage: hypercube_star.py N"""
import sys, itertools
n = int(sys.argv[1]); N = 1 << n; m = (n + 1) // 2 - 1
nb = [[v ^ (1 << i) for i in range(n)] for v in range(N)]
def ball(c): return {c, *nb[c]}
found = 0; tested = 0
reps2 = [(1 << w) - 1 for w in range(1, n + 1)]
for c2 in reps2:
    for rest in itertools.combinations([v for v in range(1, N) if v != c2], m - 2):
        cs = (0, c2) + rest; tested += 1
        U = set()
        for c in cs: U |= ball(c)
        # (2)
        bad = any(u not in cs and all(w in U for w in nb[u]) for u in U)
        if not bad:
            # (1) connectivity of Q - U
            start = next(v for v in range(N) if v not in U)
            seen = {start}; st = [start]
            while st:
                v = st.pop()
                for w in nb[v]:
                    if w not in U and w not in seen: seen.add(w); st.append(w)
            bad = len(seen) + len(U) < N
        if bad:
            found += 1
            if found <= 5: print('DISCONNECTING centres', cs, flush=True)
print('n', n, 'r', n, 'stars', m, 'centre tuples tested', tested, 'disconnecting', found)
