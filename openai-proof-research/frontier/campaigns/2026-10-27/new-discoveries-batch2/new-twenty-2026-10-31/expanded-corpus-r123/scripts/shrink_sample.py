# 346320: random search for non-confluence of each strategy on inputs built as sums of q cycles
# (scaled by q: x_e = X_e/q, y_v = Y_v/q).  Hamiltonian mode gives points of the TSP polytope.
import random, sys, json, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from shrink_exhaustive import moves, shrink, canon, terminals, STRATS
mode, n, q, trials, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
rng = random.Random(seed); found = {}; t0 = time.time(); tested = 0
for tr in range(trials):
    if time.time() - t0 > 100: break
    X = [[0] * n for _ in range(n)]
    for z in range(q):
        if mode == 'ham': s = list(range(n)); rng.shuffle(s)
        else: s = rng.sample(range(n), rng.randrange(3, n + 1))
        for u, v in zip(s, s[1:] + s[:1]): X[u][v] += 1; X[v][u] += 1
    deg = [sum(r) for r in X]
    Y = tuple(d // 2 for d in deg)
    if any(y == 0 for y in Y) or max(Y) > q: continue
    if any(X[u][v] > min(Y[u], Y[v]) for u in range(n) for v in range(n)): continue
    X = tuple(map(tuple, X)); tested += 1
    for s_ in STRATS:
        if s_ in found: continue
        T = terminals((Y, X), s_)
        if len(T) > 1:
            found[s_] = {'n': n, 'q': q, 'Y': Y, 'X': X, 'terminal_vertex_counts': sorted({len(t[0]) for t in T}), 'num_classes': len(T)}
            print('FOUND', s_, found[s_], flush=True)
    terminals.cache_clear()
print(json.dumps({'mode': mode, 'n': n, 'q': q, 'tested': tested, 'found_strategies': sorted(found)}))
