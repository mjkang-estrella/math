"""Heuristic maximisation of nonzeros in minimally AP-irreducible zero-diagonal patterns.
Exploratory only (no proof).  Local search: perturb a minimal pattern by adding random
entries, then greedily re-minimise in random order; accept if size does not drop much.
Usage: apmax.py N ITERS SEED"""
import sys, random, json, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

from apirr import ap_irr, minimal, reduce_random, show

n, iters, seed = map(int, sys.argv[1:4])
rng = random.Random(seed)
cells = [(i, j) for i in range(n) for j in range(n) if i != j]
def fresh():
    while True:
        A = {c: rng.choice((1, -1)) for c in cells if rng.random() < 0.7}
        if ap_irr(n, A):
            return reduce_random(n, A, rng)
cur = fresh(); best = dict(cur)
for t in range(iters):
    B = dict(cur)
    for c in rng.sample(cells, rng.randint(1, max(2, n))):
        B[c] = rng.choice((1, -1))
    if not ap_irr(n, B):
        continue
    B = reduce_random(n, B, rng)
    if len(B) >= len(cur) - (1 if rng.random() < 0.05 else 0):
        cur = B
    if len(cur) > len(best):
        best = dict(cur)
    if t % 2000 == 1999 and rng.random() < 0.3:
        cur = fresh()
assert ap_irr(n, best) and minimal(n, best)
print(json.dumps({'n': n, 'iters': iters, 'seed': seed, 'max_found': len(best), '2n-2': 2 * n - 2, 'pattern': show(n, best)}))
