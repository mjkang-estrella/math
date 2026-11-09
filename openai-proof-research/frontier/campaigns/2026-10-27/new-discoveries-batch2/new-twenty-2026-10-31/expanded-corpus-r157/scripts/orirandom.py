# Random underlying graphs G = K_n - H with s*(G) >= 2 not settled by Freschi-Lo, then orientation local search.
import sys, json, random, time, itertools
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
from oriexact import evaluate
n = int(sys.argv[1]); secs = float(sys.argv[2]); seed = int(sys.argv[3])
rnd = random.Random(seed); t = time.time(); stats = {}; found = None; graphs = 0
pairs = list(itertools.combinations(range(n), 2))
while time.time() - t < secs and found is None:
    # random H: add random edges while s >= 2 keeps holding (d_H(u)+d_H(v) <= n-4 on H-edges)
    H = set(); dH = [0]*n
    order = pairs[:]; rnd.shuffle(order); target = rnd.randrange(1, 3*n)
    for (a, b) in order:
        if len(H) >= target: break
        dH[a] += 1; dH[b] += 1; H.add((a, b))
        if any(dH[x] + dH[y] > n-4 for (x, y) in H):
            H.discard((a, b)); dH[a] -= 1; dH[b] -= 1
    if not H: continue
    edges = [p for p in pairs if p not in H]
    d = [n-1-dH[v] for v in range(n)]
    s = min(d[a]+d[b] for (a, b) in H) - n; T = -(-(n+s)//2); delta = min(d)
    if 2*delta >= n and delta >= T: continue
    graphs += 1
    o = [rnd.randrange(2) for _ in edges]; cur = evaluate(n, edges, o)
    for it in range(150):
        i = rnd.randrange(len(edges)); o[i] ^= 1
        v = evaluate(n, edges, o)
        if v <= cur or rnd.random() < 0.05: cur = v
        else: o[i] ^= 1
        if cur < T:
            found = {'H': sorted(H), 's': s, 'T': T, 'orientation': [list(e) if x else [e[1], e[0]] for e, x in zip(edges, o)]}; break
        if time.time() - t > secs: break
    key = f's={s},T={T}'; stats[key] = min(stats.get(key, 99), cur - T)
print(json.dumps({'n': n, 'seed': seed, 'graphs': graphs, 'min_margin_by_s': stats, 'found': found}))
