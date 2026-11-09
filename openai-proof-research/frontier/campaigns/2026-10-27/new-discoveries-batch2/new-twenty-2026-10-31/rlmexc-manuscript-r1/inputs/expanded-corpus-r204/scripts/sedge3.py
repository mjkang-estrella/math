"""chi'_S of small multigraphs under three readings of the class S (arXiv:2109.04099):
 deg  : loopless, every vertex degree in {0,2} or odd  (Delta_even <= 2; v3 line 817 / v1 line 756)
 sub  : additionally every non-empty component has an odd vertex (= subdivision of an odd graph, loops allowed
        in the odd graph; a cycle component is excluded)                          (v3 line 199 wording)
 subnl: additionally no thread of 2-vertices returns to the same odd vertex (subdivision of a LOOPLESS odd graph)
Brute force over colour-count vectors per bouquet.  usage: sedge3.py mode k n m_01 m_02 ... (pairs in lex order)"""
import sys, itertools, json
mode, k, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
pairs = list(itertools.combinations(range(n), 2)); mult = list(map(int, sys.argv[4:4 + len(pairs)]))
def valid(cnt):            # cnt[p] = multiplicity of pair p in this colour class
    deg = [0] * n
    for (u, v), c in zip(pairs, cnt): deg[u] += c; deg[v] += c
    if any(not (d == 0 or d == 2 or d % 2) for d in deg): return False
    if mode == 'deg': return True
    adj = {v: [] for v in range(n)}
    for (u, v), c in zip(pairs, cnt):
        for _ in range(c): adj[u].append(v); adj[v].append(u)
    seen = set()
    for s in range(n):
        if deg[s] == 0 or s in seen: continue
        comp = {s}; st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in comp: comp.add(y); st.append(y)
        seen |= comp
        if not any(deg[v] % 2 for v in comp): return False
    if mode == 'subnl':
        # walk each thread from an odd vertex through 2-vertices; reject if it ends where it started
        used = set()
        E = [(u, v, i) for (u, v), c in zip(pairs, cnt) for i in range(c)]
        inc = {v: [] for v in range(n)}
        for e in E: inc[e[0]].append(e); inc[e[1]].append(e)
        for s in range(n):
            if deg[s] % 2 == 0: continue
            for e in inc[s]:
                if e in used: continue
                used.add(e); cur = e[1] if e[0] == s else e[0]; prev = e
                while deg[cur] == 2:
                    nxt = [f for f in inc[cur] if f != prev][0]
                    used.add(nxt); cur = nxt[1] if nxt[0] == cur else nxt[0]; prev = nxt
                if cur == s: return False
    return True
comps = lambda m: [c for c in itertools.product(range(m + 1), repeat=k) if sum(c) == m]
sol = None; count = 0
for cs in itertools.product(*(comps(m) for m in mult)):
    if all(valid([c[j] for c in cs]) for j in range(k)):
        count += 1
        if sol is None: sol = cs
print(json.dumps(dict(mode=mode, colours=k, n=n, mult=mult, colourings=count, example=sol)))
