# Conjecture 1.6 of Ai-Guo-Gutin-Lan-Shao-Yeo-Zhou (arXiv:2501.05968v2): oriented graph D on n>=3 vertices,
# s*(D) = min{d(u)+d(v)-n : u,v non-adjacent} (n-2 for tournaments). If s*>=0 then some Hamilton oriented
# cycle C has sigma_max(C) >= ceil((n+s*)/2).  Search: all underlying graphs G = complement of H (H nonempty,
# s* >= 2; s* in {0,1} is trivial), up to isomorphism; for each G decide whether SOME orientation has every
# Hamilton cycle with sigma_+ <= T-1 and sigma_- <= T-1 (T = ceil((n+s)/2)), by exhaustive backtracking.
import sys, itertools, json, time
n = int(sys.argv[1]); smin = int(sys.argv[2]) if len(sys.argv) > 2 else 2
K = int(sys.argv[3]) if len(sys.argv) > 3 else 1; R = int(sys.argv[4]) if len(sys.argv) > 4 else 0
pairs = list(itertools.combinations(range(n), 2)); pidx = {p: i for i, p in enumerate(pairs)}
def degs(E):
    d = [0]*n
    for (a, b) in E: d[a] += 1; d[b] += 1
    return d
def okH(E):
    d = degs(E)
    return all(d[a]+d[b] <= n-2-smin for (a, b) in E)
def canon(E):
    d = degs(E)
    classes = {}
    for v in range(n): classes.setdefault(-d[v], []).append(v)
    keys = sorted(classes)
    best = None
    for combo in itertools.product(*[itertools.permutations(classes[k]) for k in keys]):
        order = [v for grp in combo for v in grp]
        lab = {v: i for i, v in enumerate(order)}
        m = 0
        for (a, b) in E:
            x, y = sorted((lab[a], lab[b])); m |= 1 << pidx[(x, y)]
        if best is None or m < best: best = m
    return best
# BFS over H
seen = {0: ()}; frontier = [()]
allH = []
while frontier:
    nf = []
    for E in frontier:
        for p in pairs:
            if p in E: continue
            E2 = tuple(sorted(E + (p,)))
            if not okH(E2): continue
            c = canon(E2)
            if c in seen: continue
            seen[c] = E2; nf.append(E2)
    allH.extend(nf); frontier = nf
def hamcycles(adj):
    cyc = []
    def rec(path, used):
        if len(path) == n:
            if path[0] in adj[path[-1]] and path[1] < path[-1]:
                cyc.append(list(path))
            return
        for w in adj[path[-1]]:
            if not used >> w & 1:
                path.append(w); rec(path, used | 1 << w); path.pop()
    rec([0], 1)
    return cyc
results = []; t = time.time(); bad_found = []
for hi, H in enumerate(allH):
    if hi % K != R: continue
    Hs = set(H)
    Gedges = [p for p in pairs if p not in Hs]
    d = degs(Gedges)
    s = min(d[a]+d[b] for (a, b) in H) - n
    T = -(-(n+s)//2)
    adj = [set() for _ in range(n)]
    for (a, b) in Gedges: adj[a].add(b); adj[b].add(a)
    cycs = hamcycles(adj)
    eidx = {p: i for i, p in enumerate(Gedges)}
    m = len(Gedges)
    # for each edge, list of (cycle, dir) ; dir=1 if cycle traverses a->b with a<b
    inc = [[] for _ in range(m)]
    for ci, C in enumerate(cycs):
        for i in range(n):
            a, b = C[i], C[(i+1) % n]
            e = eidx[(min(a, b), max(a, b))]
            inc[e].append((ci, 1 if a < b else 0))
    f = [0]*len(cycs); bk = [0]*len(cycs)
    orient = [None]*m; nodes = [0]; found = []
    def bt(e):
        nodes[0] += 1
        if e == m:
            found.append(list(orient)); return True
        for x in ((1, 0) if e > 0 else (1,)):
            ok = True; touched = []
            for (ci, dr) in inc[e]:
                if dr == x:
                    f[ci] += 1; touched.append((ci, 0))
                    if f[ci] >= T: ok = False
                else:
                    bk[ci] += 1; touched.append((ci, 1))
                    if bk[ci] >= T: ok = False
            if ok:
                orient[e] = x
                if bt(e+1): return True
            for (ci, w) in touched:
                if w == 0: f[ci] -= 1
                else: bk[ci] -= 1
        return False
    bt(0)
    rec = {'H': H, 's': s, 'T': T, 'hamcycles': len(cycs), 'nodes': nodes[0], 'bad_orientation': None}
    if found:
        rec['bad_orientation'] = [(a, b) if found[0][i] == 1 else (b, a) for i, (a, b) in enumerate(Gedges)]
        bad_found.append(rec)
    results.append(rec)
print(json.dumps({'n': n, 'smin': smin, 'shard': [K, R], 'done': len(results), 'num_H': len(allH), 'counterexamples': bad_found,
                  'max_nodes': max([r['nodes'] for r in results] or [0]), 'sec': round(time.time()-t, 1)}))
