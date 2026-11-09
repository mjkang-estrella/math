"""365134: Petersen-derived snarks via vertex->triangle and edge->digon insertions (all subsets up to
cap), checking Hamiltonian path (DFS) and non-conflicting flow existence. Usage: run_ops.py LANE MODE"""
import sys, json, pathlib, itertools, random
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N, snarklib as L

def ham_path_dfs(n, E, limit=2_000_000):
    adj = [[] for _ in range(n)]
    for u, v in E:
        if v not in adj[u]: adj[u].append(v); adj[v].append(u)
    steps = [0]
    def rec(path, seen):
        steps[0] += 1
        if steps[0] > limit: raise TimeoutError
        if len(path) == n: return True
        u = path[-1]
        for w in sorted(adj[u], key=lambda w: sum(1 for x in adj[w] if x not in seen)):
            if w not in seen:
                seen.add(w); path.append(w)
                if rec(path, seen): return True
                path.pop(); seen.discard(w)
        return False
    for s in range(n):
        if rec([s], {s}): return True
    return False

mode = sys.argv[2]
n0, E0 = L.petersen()
out = []
if mode == 'triangles':
    for k in range(1, 11):
        for S in itertools.combinations(range(10), k):
            if k not in (1, 10) and S != tuple(range(k)) and k > 3: continue
            n, E = n0, list(E0)
            for v in S: n, E = L.tri(n, E, v)
            out.append((f'P10 tri{S}', n, E))
elif mode == 'digons':
    for k in range(1, 6):
        for S in itertools.combinations(range(15), k):
            if k > 2 and S != tuple(range(k)) and S != tuple(range(0, 3 * k, 3))[:k]: continue
            n, E = n0, list(E0)
            for kk in sorted(S, reverse=True): n, E = L.digon_on(n, E, kk)
            out.append((f'P10 dig{S}', n, E))
elif mode == 'random':
    rng = random.Random(int(sys.argv[3]))
    for t in range(int(sys.argv[4])):
        n, E = n0, list(E0)
        for _ in range(rng.randint(1, 6)):
            if rng.random() < .5: n, E = L.tri(n, E, rng.randrange(n))
            else: n, E = L.digon_on(n, E, rng.randrange(len(E)))
        out.append((f'rand{t}', n, E))
cnt = {'graphs': 0, 'ham': 0, 'ham_unknown': 0, 'flow': 0, 'noflow_ham': 0}
for name, n, E in out:
    inc = N.adjacency(n, E); cnt['graphs'] += 1
    try: h = ham_path_dfs(n, E)
    except TimeoutError: h = None; cnt['ham_unknown'] += 1
    if h: cnt['ham'] += 1
    w = None
    for F in N.perfect_matchings(n, E, inc):
        w = N.flow_exists(n, E, inc, F)
        if w: break
    if w: cnt['flow'] += 1
    else:
        print('NOFLOW', name, n, 'ham', h, json.dumps(E), flush=True)
        if h: cnt['noflow_ham'] += 1
print(json.dumps({'mode': mode, **cnt}))
