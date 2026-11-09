"""Exp3: adversarial search for rank-n idempotents P on R^N with ||P||<4/3 minimizing the
fractional-packing slack s(P) = max_K t*(K) - (2-||P||) (t* = fractional allocation LP value).
Also reports the integral packing number for condition (11) of the source.
mode=any : arbitrary idempotents, moves P -> S P S^{-1}, S = I + step*G, seeds = block averages.
mode=min : P = an LP-minimal projection onto V = range [I;U] (near-cube seeds), moves on U.
OBJ=c (argv6) instead maximizes c(P)=(1-t*)/(||P||-1) over ||P||>=LMIN (argv7); FP holds iff c<=1.
Float numerics; leads only, never a proof."""
import json, random, sys, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from lib import best_fractional, integral_packing, row_norm, mat_mul, projection_constant

seed, n, N, mode, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5])
rng = random.Random(seed)
OBJ = sys.argv[6] if len(sys.argv) > 6 else 'slack'
LMIN = float(sys.argv[7]) if len(sys.argv) > 7 else 1.01

def inv(a):
    m = len(a); a = [r[:] + [float(i == j) for j in range(m)] for i, r in enumerate(a)]
    for c in range(m):
        k = max(range(c, m), key=lambda r: abs(a[r][c]))
        if abs(a[k][c]) < 1e-12: return None
        a[c], a[k] = a[k], a[c]; v = a[c][c]; a[c] = [x / v for x in a[c]]
        for r in range(m):
            if r != c:
                v = a[r][c]; a[r] = [x - v * y for x, y in zip(a[r], a[c])]
    return [r[m:] for r in a]

def seed_any():
    # random partition of [N] into n blocks, averaging projection (norm 1)
    lab = list(range(n)) + [rng.randrange(n) for _ in range(N - n)]; rng.shuffle(lab)
    P = [[0.0] * N for _ in range(N)]
    for b in range(n):
        idx = [i for i in range(N) if lab[i] == b]
        for i in idx:
            for j in idx: P[i][j] = 1.0 / len(idx)
    return P

def move_any(P, step):
    S = [[float(i == j) + rng.gauss(0, step) for j in range(N)] for i in range(N)]
    Si = inv(S)
    return None if Si is None else mat_mul(mat_mul(S, P), Si)

def P_of_U(U):
    F = [[float(i == j) for j in range(n)] for i in range(n)] + U
    lam, P = projection_constant(F)
    return P

def score(P):
    if P is None: return None
    L = row_norm(P)
    if L >= 4 / 3 - 1e-7: return None
    v, K = best_fractional(P, n)
    if OBJ == 'slack': return v - (2 - L), L, P, K
    if L < LMIN: return None
    return -(1 - v) / (L - 1), L, P, K     # minimize -c(P), c = loss coefficient

t0 = time.time(); best = None; climbs = 0; evals = 0
while time.time() - t0 < budget:
    climbs += 1
    if mode == 'any':
        cur_state = seed_any(); cur = score(cur_state)
    else:
        cur_state = [[rng.uniform(-0.6, 0.6) for _ in range(n)] for _ in range(N - n)]; cur = score(P_of_U(cur_state))
    tries = 0
    while cur is None and mode == 'any' and tries < 30:
        cur_state = move_any(cur_state, 0.08) or cur_state; cur = score(cur_state); tries += 1
    if cur is None: continue
    step = 0.15
    for it in range(60):
        if time.time() - t0 > budget: break
        if mode == 'any':
            st2 = move_any(cur_state, step); c2 = score(st2)
        else:
            st2 = [[x + rng.gauss(0, step) for x in r] for r in cur_state]; c2 = score(P_of_U(st2))
        evals += 1
        if c2 is not None and c2[0] < cur[0]: cur_state, cur = st2, c2
        else: step *= 0.96
    if best is None or cur[0] < best[0]: best = cur
s, L, P, K = best
ip = integral_packing(P, n, 2 - L)
print(json.dumps({'seed': seed, 'n': n, 'N': N, 'mode': mode, 'climbs': climbs, 'evals': evals,
                  'objective': OBJ, 'value': s, 'loss_coefficient_c': (-s if OBJ == 'c' else None), 'norm': L, 'K': K, 'integral_packing_number': ip, 'P': P}, indent=1))
