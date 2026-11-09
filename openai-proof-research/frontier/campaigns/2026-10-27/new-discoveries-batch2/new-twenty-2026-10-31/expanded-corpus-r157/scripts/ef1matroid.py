# Conjecture 2 (Anholcer-Bartkowiak-Bosek-Grytczuk arXiv:2606.11494): matroid M on goods E, chi(M) <= n,
# n agents with additive valuations => an EF1 partition of E into n independent sets.
# Adversarial local search over integer valuations; exhaustive check over all independent n-partitions.
import sys, json, random, time, itertools
def graphic(edges):
    m = len(edges)
    def indep(S):
        parent = {}
        def f(x):
            while parent.get(x, x) != x: x = parent[x]
            return x
        for i in S:
            a, b = edges[i]; ra, rb = f(a), f(b)
            if ra == rb: return False
            parent[ra] = rb
        return True
    return m, indep
def linear_gf2(vecs):
    m = len(vecs)
    def indep(S):
        basis = []
        for i in S:
            v = vecs[i]
            for b in basis: v = min(v, v ^ b)
            if v == 0: return False
            basis.append(v)
        return True
    return m, indep
MATS = {
  'K4': graphic([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]),
  'K33': graphic([(a,b) for a in range(3) for b in range(3,6)]),
  'K5': graphic(list(itertools.combinations(range(5), 2))),
  'W4': graphic([(0,1),(1,2),(2,3),(3,0),(4,0),(4,1),(4,2),(4,3)]),
  'F7': linear_gf2([1,2,3,4,5,6,7]),
  'F7star': None,
}
name, n, secs, seed, vmax = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
m, indep = MATS[name]
# all independent sets as bitmasks
ind = set()
for r in range(m+1):
    for S in itertools.combinations(range(m), r):
        if indep(S): ind.add(sum(1 << i for i in S))
# all ordered partitions into n independent sets (assignment vectors)
parts = []
for assign in itertools.product(range(n), repeat=m):
    bundles = [0]*n
    for i, a in enumerate(assign): bundles[a] |= 1 << i
    if all(b in ind for b in bundles): parts.append(bundles)
def viol(vals, bundles):
    worst = -10**9
    for i in range(n):
        vi = vals[i]; own = sum(vi[g] for g in range(m) if bundles[i] >> g & 1)
        for j in range(n):
            if i == j or not bundles[j]: continue
            items = [vi[g] for g in range(m) if bundles[j] >> g & 1]
            w = sum(items) - max(items) - own
            if w > worst: worst = w
    return worst
def score(vals):
    return min(viol(vals, b) for b in parts)   # > 0 means no EF1 partition: counterexample
rnd = random.Random(seed); t = time.time(); best = -10**9; found = None; evals = 0
while time.time() - t < secs and found is None:
    vals = [[rnd.randint(0, vmax) for _ in range(m)] for _ in range(n)]; cur = score(vals); evals += 1
    for it in range(200):
        i = rnd.randrange(n); g = rnd.randrange(m); old = vals[i][g]; vals[i][g] = rnd.randint(0, vmax)
        v = score(vals); evals += 1
        if v >= cur or rnd.random() < 0.03: cur = v
        else: vals[i][g] = old
        best = max(best, cur)
        if cur > 0: found = vals; break
        if time.time() - t > secs: break
print(json.dumps({'matroid': name, 'n': n, 'partitions': len(parts), 'evals': evals, 'best_min_violation': best, 'found': found}))
