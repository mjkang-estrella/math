"""Exhaustive test of Petrusevski-Skrekovski Conjecture conj:3 (arXiv:2109.04099 v1-v3; MathDB 351888):
S = graphs with Delta_even <= 2 (every vertex has degree 0, 2 or odd in the colour class); chi'_S(G) = min colours
such that every colour class is in S.  Conjecture: connected loopless G that is not a Shannon triangle of type (2,2,1)
with multiplicity >= 3 has chi'_S(G) <= 3.
Multigraph = multiplicity vector on vertex pairs; a colouring is a choice of colour counts (c1,c2,c3) per bouquet.
usage: sedge.py n M   (all multiplicity vectors on the C(n,2) pairs with entries 0..M, connected)"""
import sys, itertools, json
n, M = int(sys.argv[1]), int(sys.argv[2])
pairs = list(itertools.combinations(range(n), 2))
comps = {m: [(a, b, m - a - b) for a in range(m + 1) for b in range(m + 1 - a)] for m in range(M + 1)}
def ok(d): return d == 0 or d == 2 or d % 2 == 1
def colourable(mult, k=3):
    bq = [(p, m) for p, m in zip(pairs, mult) if m > 0]
    last = {}
    for idx, (p, m) in enumerate(bq):
        for v in p: last[v] = idx
    deg = [[0] * 3 for _ in range(n)]
    def rec(i):
        if i == len(bq): return True
        (u, v), m = bq[i]
        for c in comps[m]:
            if k == 2 and c[2]: continue
            for j in range(3): deg[u][j] += c[j]; deg[v][j] += c[j]
            good = all(ok(deg[w][j]) for w in (u, v) if last[w] == i for j in range(3))
            if good and rec(i + 1): return True
            for j in range(3): deg[u][j] -= c[j]; deg[v][j] -= c[j]
        return False
    return rec(0)
def connected(mult):
    adj = {v: set() for v in range(n)}
    for (u, v), m in zip(pairs, mult):
        if m: adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == n
def shannon221(mult):
    if n != 3 or min(mult) == 0: return False
    par = sorted((m % 2 == 0) for m in mult)  # True = even
    return par == [False, True, True] and max(mult) >= 3
tested = 0; bad = []; excl = 0; seen = set()
for mult in itertools.product(range(M + 1), repeat=len(pairs)):
    if not connected(mult): continue
    key = min(tuple(mult[pairs.index(tuple(sorted((perm[a], perm[b]))))] for (a, b) in pairs) for perm in itertools.permutations(range(n)))
    if key in seen: continue
    seen.add(key); tested += 1
    c3 = colourable(mult)
    if shannon221(mult):
        excl += 1
        if c3: bad.append(('EXCLUDED_BUT_3COLOURABLE', mult))
        continue
    if not c3: bad.append(('NEEDS4', mult))
print(json.dumps(dict(n=n, M=M, iso_classes_tested=tested, excluded_shannon221=excl, anomalies=len(bad), first=bad[:20])))
