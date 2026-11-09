# Targeted MathDB 388092 search decided exactly by HiGHS MILP; feasible answers are re-verified combinatorially.
# Instances: c=p/N, N in [4,12], k in {3,4}; configuration-model bipartite multigraphs (or simple graphs if 'simple'),
# degrees mixing multiples of N (all colours exact) with arbitrary residues. Usage: seed trials workers mode
import sys, json, random
from multiprocessing import Pool
sys.path.insert(0, sys.argv[5])
from propfactor_milp import decide
def gen(seed, simple):
    rng = random.Random(seed)
    k = rng.randint(3, 4); N = rng.randint(max(4, k), 12)
    cuts = sorted(rng.sample(range(1, N), k - 1)); p = [x - y for x, y in zip(cuts + [N], [0] + cuts)]
    a, b = rng.randint(2, 7), rng.randint(2, 7)
    if simple:
        E = [(i, a + j) for i in range(a) for j in range(b) if rng.random() < rng.uniform(0.4, 1.0)]
        return a, b, E, p, N
    pick = lambda: N * rng.randint(1, 2) if rng.random() < 0.5 else rng.randint(1, 2 * N)
    da = [pick() for _ in range(a)]; db = [pick() for _ in range(b)]
    while sum(da) != sum(db):
        if sum(da) < sum(db): da[rng.randrange(a)] += 1
        else: db[rng.randrange(b)] += 1
    A = [i for i, d in enumerate(da) for _ in range(d)]; B = [a + j for j, d in enumerate(db) for _ in range(d)]
    rng.shuffle(B)
    return a, b, list(zip(A, B)), p, N
def work(args):
    seed, simple = args
    a, b, E, p, N = gen(seed, simple)
    if not E or len(E) > 90: return None
    r = decide(a, b, E, p, N)
    return None if r == 'feasible-verified' else {'result': r, 'seed': seed, 'a': a, 'b': b, 'E': E, 'p': p, 'N': N}
if __name__ == '__main__':
    seed, trials, workers, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    bad = 0
    with Pool(workers) as P:
        for r in P.imap_unordered(work, [(seed * 10**7 + t, mode == 'simple') for t in range(trials)], chunksize=50):
            if r: bad += 1; print(json.dumps(r)); sys.stdout.flush()
    print(json.dumps({'finished': True, 'seed': seed, 'trials': trials, 'mode': mode, 'non_feasible': bad}))
