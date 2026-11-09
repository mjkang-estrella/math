"""Exp4: adversarially maximize the loss coefficient c=(1-value)/(||P||-1) for explicit SELECTION RULES.
 R = Auerbach set: n coordinates maximizing |det B_R| for a basis B of V=range P; normalize B_R=I.
 rule 'lp'  : best fractional allocation for agents R (LP).
 rule 'geo' : explicit allocation w_kj = |B_jk| / max(1, sum_k |B_jk|), agents R.
 rule 'self': explicit allocation w_kj = |p_jk| / sum_{k' in R} |p_jk'|, agents R.
A rule 'works' on P iff its value >= 2-||P||, i.e. c<=1.  Float numerics; leads only."""
import itertools, json, random, sys, time
sys.path.insert(0, __import__('os').path.dirname(__file__))
from lib import fractional_value, row_norm, mat_mul, projection_constant

seed, n, N, mode, rule, budget = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5], float(sys.argv[6])
LMIN = 1.01
rng = random.Random(seed)

def det(a):
    a = [r[:] for r in a]; m = len(a); d = 1.0
    for c in range(m):
        k = max(range(c, m), key=lambda r: abs(a[r][c]))
        if abs(a[k][c]) < 1e-14: return 0.0
        if k != c: a[c], a[k] = a[k], a[c]; d = -d
        d *= a[c][c]
        for r in range(c + 1, m):
            f = a[r][c] / a[c][c]; a[r] = [x - f * y for x, y in zip(a[r], a[c])]
    return d

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

def basis(P):
    # columns of P spanning V: pick a column set with nonsingular n x n minor somewhere
    for K in itertools.combinations(range(N), n):
        Bc = [[P[i][j] for j in K] for i in range(N)]
        if max(abs(det([Bc[i] for i in R])) for R in itertools.combinations(range(N), n)) > 1e-9: return Bc
    return None

def evaluate(P):
    Bc = basis(P)
    R = max(itertools.combinations(range(N), n), key=lambda R: abs(det([Bc[i] for i in R])))
    Ri = inv([Bc[i] for i in R]); B = mat_mul(Bc, Ri)          # B_R = I, |B_jk| <= 1 (Cramer)
    if rule == 'lp': return fractional_value(P, list(R)), R
    if rule == 'geo':
        vals = []
        for a, k in enumerate(R):
            vals.append(sum(abs(P[k][j]) * abs(B[j][a]) / max(1.0, sum(abs(x) for x in B[j])) for j in range(N)))
        return min(vals), R
    if rule == 'self':
        vals = []
        for k in R:
            v = 0.0
            for j in range(N):
                s = sum(abs(P[j][kk]) for kk in R)
                if s > 1e-15: v += abs(P[k][j]) * abs(P[j][k]) / s
            vals.append(v)
        return min(vals), R

def seed_any():
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
    return projection_constant([[float(i == j) for j in range(n)] for i in range(n)] + U)[1]

def score(P):
    if P is None: return None
    L = row_norm(P)
    if L >= 4 / 3 - 1e-7 or L < LMIN: return None
    v, R = evaluate(P)
    return (1 - v) / (L - 1), L, P, R

t0 = time.time(); best = None; climbs = 0; worst_fail = []
while time.time() - t0 < budget:
    climbs += 1
    if mode == 'any':
        st = seed_any(); cur = None; tries = 0
        while cur is None and tries < 30:
            st = move_any(st, 0.08) or st; cur = score(st); tries += 1
    else:
        st = [[rng.uniform(-0.6, 0.6) for _ in range(n)] for _ in range(N - n)]; cur = score(P_of_U(st))
    if cur is None: continue
    step = 0.15
    for it in range(50):
        if time.time() - t0 > budget: break
        st2 = move_any(st, step) if mode == 'any' else [[x + rng.gauss(0, step) for x in r] for r in st]
        c2 = score(st2 if mode == 'any' else P_of_U(st2))
        if c2 is not None and c2[0] > cur[0]: st, cur = st2, c2
        else: step *= 0.96
    if best is None or cur[0] > best[0]: best = cur
c, L, P, R = best
print(json.dumps({'seed': seed, 'n': n, 'N': N, 'mode': mode, 'rule': rule, 'climbs': climbs,
                  'max_loss_coefficient': c, 'rule_fails': c > 1, 'norm': L, 'R': R, 'P': P}, indent=1))
