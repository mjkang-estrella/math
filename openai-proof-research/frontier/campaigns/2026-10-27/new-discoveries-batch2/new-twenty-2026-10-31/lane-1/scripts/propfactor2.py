# Broader random search (MathDB 388092): larger bipartite (multi)graphs, k in {3,4,5}, c with denominators up to 40.
import sys, random, json
from fractions import Fraction as F
sys.path.insert(0, sys.argv[5])
from propfactor import solvable
seed = int(sys.argv[1]); trials = int(sys.argv[2]); maxside = int(sys.argv[3]); maxmult = int(sys.argv[4])
rng = random.Random(seed)
for t in range(trials):
    k = rng.choice([3, 3, 4, 5])
    a, b = rng.randint(2, maxside), rng.randint(2, maxside)
    E = []
    p = rng.uniform(0.3, 1.0)
    for i in range(a):
        for j in range(b):
            if rng.random() < p: E += [(i, a + j)] * rng.randint(1, maxmult)
    if not E: continue
    N = rng.randint(k + 1, 40)
    cuts = sorted(rng.sample(range(1, N), k - 1))
    c = [F(x - y, N) for x, y in zip(cuts + [N], [0] + cuts)]
    if not solvable(a + b, E, c):
        print(json.dumps({'COUNTEREXAMPLE': True, 'nv': a + b, 'a': a, 'edges': E, 'c': [str(x) for x in c]})); sys.stdout.flush()
print(json.dumps({'done': trials, 'seed': seed, 'maxside': maxside, 'maxmult': maxmult}))
