# Same search as oridisc.py, with (a) Freschi-Lo skip: if delta >= n/2 and delta >= T the graph is settled by
# Theorem 1.1 (Freschi-Lo), and (b) propagation: a cycle with T-1 arcs in one direction forces its remaining
# arcs into the other direction.  Sharded: n smin K R.
import sys, itertools, json, time
n = int(sys.argv[1]); smin = int(sys.argv[2]); K = int(sys.argv[3]); R = int(sys.argv[4]); NODELIM = int(sys.argv[5]) if len(sys.argv) > 5 else 10**9
pairs = list(itertools.combinations(range(n), 2)); pidx = {p: i for i, p in enumerate(pairs)}
def degs(E):
    d = [0]*n
    for (a, b) in E: d[a] += 1; d[b] += 1
    return d
def okH(E):
    d = degs(E)
    return all(d[a]+d[b] <= n-2-smin for (a, b) in E)
def canon(E):
    d = degs(E); classes = {}
    for v in range(n):
        if d[v] == 0: continue
        classes.setdefault((-d[v], tuple(sorted(-d[w] for (a,b) in E for w in (a,b) if v in (a,b) and w != v))), []).append(v)
    keys = sorted(classes); best = None
    for combo in itertools.product(*[itertools.permutations(classes[k]) for k in keys]):
        order = [v for grp in combo for v in grp]; lab = {v: i for i, v in enumerate(order)}; m = 0
        for (a, b) in E:
            x, y = sorted((lab[a], lab[b])); m |= 1 << pidx[(x, y)]
        if best is None or m < best: best = m
    return best
seen = {0}; frontier = [()]; allH = []
while frontier:
    nf = []
    for E in frontier:
        for p in pairs:
            if p in E: continue
            E2 = tuple(sorted(E + (p,)))
            if not okH(E2): continue
            c = canon(E2)
            if c in seen: continue
            seen.add(c); nf.append(E2)
    allH.extend(nf); frontier = nf
def hamcycles(adj):
    cyc = []
    def rec(path, used):
        if len(path) == n:
            if path[0] in adj[path[-1]] and path[1] < path[-1]: cyc.append(list(path))
            return
        for w in adj[path[-1]]:
            if not used >> w & 1:
                path.append(w); rec(path, used | 1 << w); path.pop()
    rec([0], 1); return cyc
print('H enumerated', len(allH), flush=True)
t = time.time(); out = []; bad = []; skipped = 0
for hi, H in enumerate(allH):
    if hi % K != R: continue
    Hs = set(H); Gedges = [p for p in pairs if p not in Hs]; d = degs(Gedges)
    s = min(d[a]+d[b] for (a, b) in H) - n; T = -(-(n+s)//2); delta = min(d)
    if 2*delta >= n and delta >= T:
        skipped += 1; out.append({'H': H, 's': s, 'T': T, 'status': 'Freschi-Lo'}); continue
    adj = [set() for _ in range(n)]
    for (a, b) in Gedges: adj[a].add(b); adj[b].add(a)
    cycs = hamcycles(adj); eidx = {p: i for i, p in enumerate(Gedges)}; m = len(Gedges)
    inc = [[] for _ in range(m)]; cyc_edges = []
    for ci, C in enumerate(cycs):
        ce = []
        for i in range(n):
            a, b = C[i], C[(i+1) % n]; e = eidx[(min(a, b), max(a, b))]; dr = 1 if a < b else 0
            inc[e].append((ci, dr)); ce.append((e, dr))
        cyc_edges.append(ce)
    cnt = [[0, 0] for _ in cycs]   # cnt[ci][x] = number of arcs of C currently matching direction x (x=1 forward)
    orient = [None]*m; nodes = [0]
    def assign(e, x, trail):
        # returns False on conflict; pushes to trail
        stack = [(e, x)]
        while stack:
            e, x = stack.pop()
            if orient[e] is not None:
                if orient[e] != x: return False
                continue
            orient[e] = x; trail.append(e)
            for (ci, dr) in inc[e]:
                cnt[ci][1 if dr == x else 0] += 1
            for (ci, dr) in inc[e]:
                side = 1 if dr == x else 0
                if cnt[ci][side] >= T: return False
                if cnt[ci][side] == T-1:
                    for (e2, dr2) in cyc_edges[ci]:
                        if orient[e2] is None:
                            # e2 must NOT go in direction 'side' along C: orientation x2 with (dr2==x2) != side
                            x2 = dr2 if side == 0 else 1-dr2
                            stack.append((e2, x2))
        return True
    def undo(trail):
        while trail:
            e = trail.pop(); x = orient[e]
            for (ci, dr) in inc[e]:
                cnt[ci][1 if dr == x else 0] -= 1
            orient[e] = None
    class Lim(Exception): pass
    def bt():
        nodes[0] += 1
        if nodes[0] > NODELIM: raise Lim()
        e = next((i for i in range(m) if orient[i] is None), None)
        if e is None: return True
        for x in (1, 0):
            trail = []
            if assign(e, x, trail) and bt(): return True
            undo(trail)
        return False
    trail0 = []
    try:
        ok = assign(0, 1, trail0) and bt(); st = 'counterexample' if ok else 'holds'
    except Lim:
        ok = False; st = 'undecided'
    rec = {'H': H, 's': s, 'T': T, 'delta': delta, 'hamcycles': len(cycs), 'nodes': nodes[0], 'status': st}
    if ok:
        rec['orientation'] = [(a, b) if orient[i] == 1 else (b, a) for i, (a, b) in enumerate(Gedges)]
        bad.append(rec)
    out.append(rec); print(hi, rec['s'], rec['T'], rec.get('hamcycles'), rec.get('nodes'), rec['status'], round(time.time()-t,1), flush=True)
    if time.time() - t > 100: break
json.dump(out, open(f'outputs/oridisc-n{n}-s{smin}-K{K}-R{R}.json','w'))
print(json.dumps({'n': n, 'smin': smin, 'shard': [K, R], 'num_H_total': len(allH), 'processed': len(out), 'skipped_FL': skipped,
                  'counterexamples': bad, 'max_nodes': max([r.get('nodes', 0) for r in out] or [0]), 'sec': round(time.time()-t, 1)}))
