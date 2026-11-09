"""Exp2: adversarial hill-climb over 2-dim V in l_inf^N maximizing rho=(d-1)/(lam/(4-3lam)-1), LMIN<=lam<4/3 (LMIN=argv4, default 1.002).
rho>1 would be a violation of Conjecture 1.1.  d is a multistart upper estimate, so a reported r>1
is only a lead requiring rigorous re-evaluation.  Float numerics; support evidence only."""
import json, math, random, sys, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from lib import projection_constant, bm_distance_2d

seed, N, budget = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
LMIN = float(sys.argv[4]) if len(sys.argv) > 4 else 1.002
rng = random.Random(seed)

def score(F):
    lam, _ = projection_constant(F)
    if lam is None or lam >= 4 / 3 - 1e-6 or lam < LMIN: return -1, lam, None
    d, _ = bm_distance_2d(F, rng, restarts=14, iters=250)
    return (d - 1) / (lam / (4 - 3 * lam) - 1), lam, d

def rand_F():
    F = [[1.0, 0.0], [0.0, 1.0]]
    for _ in range(N - 2):
        th = rng.uniform(0, math.pi); r = rng.uniform(0.6, 1.3)
        F.append([r * math.cos(th), r * math.sin(th)])
    return F

t0 = time.time(); hist = []
best = (-1, None, None, None)
while time.time() - t0 < budget:
    F = rand_F(); s, lam, d = score(F); step = 0.1
    for it in range(60):
        if time.time() - t0 > budget: break
        G = [row[:] for row in F]
        j = rng.randrange(2, N); G[j] = [G[j][0] + rng.gauss(0, step), G[j][1] + rng.gauss(0, step)]
        s2, lam2, d2 = score(G)
        if s2 > s: F, s, lam, d = G, s2, lam2, d2
        else: step *= 0.97
    hist.append((s, lam, d))
    if s > best[0]: best = (s, lam, d, F)
# heavy re-evaluation of the best
s, lam, d, F = best
dh, _ = bm_distance_2d(F, random.Random(99), restarts=200, iters=1500)
print(json.dumps({'seed': seed, 'N': N, 'climbs': len(hist), 'best_ratio_quick': s, 'lam': lam,
                  'd_quick': d, 'd_heavy': dh, 'rho_heavy': (dh - 1) / (lam / (4 - 3 * lam) - 1), 'violation_if_rho_gt_1': True, 'F': F,
                  'top_climbs': sorted(hist, reverse=True)[:5]}, indent=1))
