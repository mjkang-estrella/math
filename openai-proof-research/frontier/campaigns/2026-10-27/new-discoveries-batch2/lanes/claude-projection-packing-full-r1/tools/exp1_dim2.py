"""Exp1: two-dimensional V in l_inf^N, N=5..8 (codimension >= 3, outside the source theorem).
Float lambda (LP) and float BM distance (multistart local search: an UPPER estimate of d).
Prints sanity cases and the largest observed ratio d*(4-3*lambda)/lambda for lambda<4/3."""
import json, math, random, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from lib import projection_constant, bm_distance_2d, best_fractional

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
trials = int(sys.argv[2]) if len(sys.argv) > 2 else 40
out = {'sanity': {}, 'worst': []}
hexa = [[1, 0], [0.5, math.sqrt(3) / 2], [-0.5, math.sqrt(3) / 2]]
sq = [[1, 0], [0, 1], [0.5, 0.5], [0.5, -0.5], [0.3, 0.7]]
for name, F in [('hexagon', hexa), ('square+inner', sq)]:
    lam, P = projection_constant(F); d, _ = bm_distance_2d(F, rng)
    out['sanity'][name] = (lam, d)
rows = []
for t in range(trials):
    N = rng.choice([5, 6, 7])
    # near-square family: two cube functionals plus N-2 cut functionals of l1-size 1+eta*c
    eta = rng.choice([0.02, 0.05, 0.1, 0.2])
    F = [[1.0, 0.0], [0.0, 1.0]]
    for _ in range(N - 2):
        th = rng.uniform(0, 2 * math.pi); u = (math.cos(th), math.sin(th)); s = abs(u[0]) + abs(u[1])
        mode = rng.random()
        if mode < 0.5:   # cut near the diamond boundary
            r = (1 + eta * rng.uniform(-0.2, 1)) / s
        else:            # cluster near a vertex of the diamond (degenerate first order)
            k = rng.randrange(2); u = [0.0, 0.0]; u[k] = 1.0; u[1 - k] = rng.uniform(-eta, eta); r = 1 + eta * rng.uniform(0, 1)
            u = tuple(u)
        F.append([r * u[0], r * u[1]])
    lam, P = projection_constant(F)
    if lam is None or lam >= 4 / 3 - 1e-9: continue
    d, _ = bm_distance_2d(F, rng, restarts=25, iters=300)
    bound = lam / (4 - 3 * lam)
    fp, K = best_fractional(P, 2)
    rows.append({'N': N, 'lam': lam, 'd_upper_est': d, 'bound': bound, 'ratio': d / bound,
                 'fp_minus_need': fp - (2 - lam), 'F': F})
rows.sort(key=lambda r: -r['ratio'])
out['worst'] = rows[:5]
out['max_ratio'] = rows[0]['ratio'] if rows else None
out['min_fp_slack'] = min(r['fp_minus_need'] for r in rows) if rows else None
out['count'] = len(rows)
print(json.dumps(out, indent=1))
