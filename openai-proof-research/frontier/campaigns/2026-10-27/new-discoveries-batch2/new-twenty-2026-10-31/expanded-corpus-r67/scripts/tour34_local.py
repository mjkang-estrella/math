# Diagnostic for MathDB 372373: local search over n-vertex (3,4)-tournaments minimising the number of
# spanning tight paths (exact DP count).  A zero would be a counterexample candidate; otherwise this
# is only a bounded non-finding.  Usage: tour34_local.py n seconds seed
import itertools, random, sys, time, json, pathlib
n, budget, seed = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
triples = list(itertools.combinations(range(n), 3))
perms = {S: list(itertools.permutations(S)) for S in triples}
choices = list(itertools.combinations(range(6), 4))
def edges(state):
    E = set()
    for S, c in zip(triples, state):
        for i in choices[c]: E.add(perms[S][i])
    return E
def count(E):
    # f[(mask,a,b)] = number of tight paths with vertex set mask ending ...a,b
    f = {}
    for a in range(n):
        for b in range(n):
            if a != b: f[((1 << a) | (1 << b), a, b)] = 1
    for _ in range(n - 2):
        g = {}
        for (m, a, b), v in f.items():
            for c in range(n):
                if not (m >> c) & 1 and (a, b, c) in E:
                    k = (m | (1 << c), b, c); g[k] = g.get(k, 0) + v
        f = g
    return sum(f.values())
t0 = time.monotonic(); best = None; restarts = 0; hist = []
while time.monotonic() - t0 < budget:
    restarts += 1
    st = [rng.randrange(15) for _ in triples]; cur = count(edges(st)); stall = 0
    while stall < 150 and time.monotonic() - t0 < budget:
        i = rng.randrange(len(st)); old = st[i]; st[i] = rng.randrange(15)
        v = count(edges(st))
        if v <= cur: cur = v; stall = 0 if v < cur else stall + 1
        else: st[i] = old; stall += 1
        if cur == 0: break
    hist.append(cur)
    if best is None or cur < best[0]: best = (cur, list(st))
    if cur == 0: break
res = dict(n=n, seed=seed, seconds=time.monotonic() - t0, restarts=restarts, min_spanning_paths=best[0], conjectured_min=2 ** (n - 1), restart_minima=hist)
print(json.dumps(res))
p = pathlib.Path(__file__).resolve().parents[1] / f'outputs/tour34_local_n{n}_s{seed}.json'; p.write_text(json.dumps(dict(res, best_state=best[1]), indent=1) + '\n')
