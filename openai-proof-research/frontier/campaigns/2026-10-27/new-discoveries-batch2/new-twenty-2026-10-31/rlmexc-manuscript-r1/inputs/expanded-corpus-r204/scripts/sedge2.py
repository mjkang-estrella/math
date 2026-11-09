"""For all connected loopless multigraphs on n vertices with multiplicities 0..M (up to isomorphism), compute
whether chi'_S <= 2 and <= 3 (S = loopless, Delta_even <= 2, arXiv:2109.04099 line 817). usage: sedge2.py n M"""
import sys, itertools, json
n, M = int(sys.argv[1]), int(sys.argv[2])
pairs = list(itertools.combinations(range(n), 2)); P = len(pairs)
def comps(m, k): return [c for c in itertools.product(range(m + 1), repeat=k) if sum(c) == m]
CC = {(m, k): comps(m, k) for m in range(M + 1) for k in (2, 3)}
ok = lambda d: d == 0 or d == 2 or d % 2 == 1
def colourable(mult, k):
    bq = [(p, m) for p, m in zip(pairs, mult) if m > 0]
    last = {}
    for i, (p, m) in enumerate(bq):
        for v in p: last[v] = i
    deg = [[0] * k for _ in range(n)]
    def rec(i):
        if i == len(bq): return True
        (u, v), m = bq[i]
        for c in CC[(m, k)]:
            for j in range(k): deg[u][j] += c[j]; deg[v][j] += c[j]
            if all(ok(deg[w][j]) for w in (u, v) if last[w] == i for j in range(k)) and rec(i + 1): return True
            for j in range(k): deg[u][j] -= c[j]; deg[v][j] -= c[j]
        return False
    return rec(0)
def connected(mult):
    adj = {v: set() for v in range(n)}
    for (u, v), m in zip(pairs, mult):
        if m: adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x] - seen: seen.add(y); st.append(y)
    return len(seen) == n
perms = list(itertools.permutations(range(n)))
pidx = {p: i for i, p in enumerate(pairs)}
maps = [[pidx[tuple(sorted((pm[a], pm[b])))] for (a, b) in pairs] for pm in perms]
seen = set(); stats = {'tested': 0, 'not2': 0, 'not3': 0}; not2 = []; not3 = []
for mult in itertools.product(range(M + 1), repeat=P):
    if not connected(mult): continue
    key = min(tuple(mult[mp[i]] for i in range(P)) for mp in maps)
    if key in seen: continue
    seen.add(key); stats['tested'] += 1
    if not colourable(mult, 2):
        stats['not2'] += 1; not2.append(mult)
        if not colourable(mult, 3): stats['not3'] += 1; not3.append(mult)
print(json.dumps(dict(n=n, M=M, **stats, not2_first=not2[:30], not3_list=not3[:30])))
