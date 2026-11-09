"""Capped exact checks for the Tyszka Conjecture 3 bridge (math/0702558v86, printed p21).
Finite exact controls only; they are NOT a proof. Exact integer/Fraction arithmetic.
usage: checker.py OUT.json"""
import sys, json, random, itertools
from fractions import Fraction as Fr

random.seed(20261030)
OUT = {}

def det(M):
    M = [[Fr(x) for x in r] for r in M]; n = len(M); d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f: M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return d

def rank(M):
    M = [[Fr(x) for x in r] for r in M]; rk = 0; cols = len(M[0]) if M else 0
    for c in range(cols):
        p = next((r for r in range(rk, len(M)) if M[r][c] != 0), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        for r in range(len(M)):
            if r != rk and M[r][c]:
                f = M[r][c] / M[rk][c]; M[r] = [a - f * b for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk

def all_eqs(n):
    """Allowed equations as (row, rhs): xi=1 and xi+xj=xk (all i,j,k incl. coincidences)."""
    E = []
    for i in range(n):
        r = [0] * n; r[i] = 1; E.append((tuple(r), 1, ('one', i)))
    for i in range(n):
        for j in range(i, n):
            for k in range(n):
                r = [0] * n; r[i] += 1; r[j] += 1; r[k] -= 1
                E.append((tuple(r), 0, ('add', i, j, k)))
    return E

def sat(eq, x):
    r, b, _ = eq
    return sum(a * v for a, v in zip(r, x)) == b

# 1. simple-row determinant lemma
c1 = 0
for _ in range(3000):
    m = random.randint(1, 6); M = []
    for _ in range(m):
        r = [0] * m; t = random.random()
        if t < .45:
            i, j = random.sample(range(m), 2) if m > 1 else (0, 0)
            r[i] += 1; r[j] -= 1
        elif t < .9:
            r[random.randrange(m)] = random.choice([1, -1])
        M.append(r)
    assert det(M) in (-1, 0, 1); c1 += 1
OUT['simple_row_det_in_{0,+-1}'] = c1

# 2. minor bound <= 2^(m-1) for independent row sets containing an x_i=1 row; (A_R,b_R) and A_R
c2 = 0; worst = {}
for _ in range(1500):
    n = random.randint(1, 5); E = all_eqs(n)
    ones = [e for e in E if e[2][0] == 'one']; R = [random.choice(ones)]
    pool = E[:]; random.shuffle(pool)
    for e in pool:
        if rank([list(f[0]) for f in R + [e]]) == len(R) + 1: R.append(e)
        if len(R) == n or random.random() < .05: break
    m = len(R); Ab = [list(e[0]) + [e[1]] for e in R]
    mx = 0
    for cols in itertools.combinations(range(n + 1), m):
        mx = max(mx, abs(det([[row[c] for c in cols] for row in Ab])))
    assert mx <= 2 ** (m - 1), (R, mx)
    worst[m] = max(worst.get(m, 0), int(mx)); c2 += 1
OUT['minor_bound_checks'] = c2; OUT['max_minor_seen_by_rank'] = worst

# 3. constructive BFRT pipeline on H=(1/q)Z
def bfrt(A, c):
    """A: m x n full row rank integer, c integer m-vector with an integer solution.
    Returns integer x with Ax=c, |x_j| <= Y, following the BFRT proof (Gomory shortest word by BFS)."""
    m, n = len(A), len(A[0])
    for Bc in itertools.combinations(range(n), m):
        if det([[A[r][j] for j in Bc] for r in range(m)]) != 0: break
    Nc = [j for j in range(n) if j not in Bc]
    B = [[Fr(A[r][j]) for j in Bc] for r in range(m)]
    # inverse of B
    aug = [B[r] + [Fr(int(r == s)) for s in range(m)] for r in range(m)]
    for col in range(m):
        p = next(r for r in range(col, m) if aug[r][col] != 0); aug[col], aug[p] = aug[p], aug[col]
        pv = aug[col][col]; aug[col] = [v / pv for v in aug[col]]
        for r in range(m):
            if r != col and aug[r][col]:
                f = aug[r][col]; aug[r] = [a - f * b for a, b in zip(aug[r], aug[col])]
    Bi = [row[m:] for row in aug]
    mul = lambda v: [sum(Bi[r][s] * v[s] for s in range(m)) for r in range(m)]
    frac = lambda v: tuple(x - (x.numerator // x.denominator) for x in v)
    target = frac(mul(c)); gens = [frac(mul([A[r][j] for r in range(m)])) for j in Nc]
    start = tuple(Fr(0) for _ in range(m)); prev = {start: None}; queue = [start]; qi = 0
    while target not in prev:
        u = queue[qi]; qi += 1
        for gi, g in enumerate(gens):
            w = frac([a + b for a, b in zip(u, g)])
            if w not in prev: prev[w] = (u, gi); queue.append(w)
    xN = [0] * len(Nc); u = target
    while prev[u] is not None:
        u, gi = prev[u]; xN[gi] += 1
    delta = abs(det([[A[r][j] for j in Bc] for r in range(m)]))
    assert sum(xN) <= delta - 1
    rhs = [c[r] - sum(A[r][Nc[t]] * xN[t] for t in range(len(Nc))) for r in range(m)]
    xB = mul(rhs); assert all(v.denominator == 1 for v in xB)
    x = [0] * n
    for t, j in enumerate(Bc): x[j] = int(xB[t])
    for t, j in enumerate(Nc): x[j] = xN[t]
    return x

c3 = 0; ratios = []
for _ in range(800):
    n = random.randint(1, 5); q = random.choice([1, 2, 3, 4, 6, 12])
    x0 = [Fr(1)] + [Fr(random.randint(-60, 60), q) for _ in range(n - 1)]
    random.shuffle(x0)
    E = [e for e in all_eqs(n) if sat(e, x0)]
    S = random.sample(E, min(len(E), random.randint(1, 2 * n)))
    if not any(e[2][0] == 'one' for e in S):
        S.append(next(e for e in E if e[2][0] == 'one'))
    R = [next(e for e in S if e[2][0] == 'one')]
    for e in S:
        if rank([list(f[0]) for f in R + [e]]) == len(R) + 1: R.append(e)
    A = [list(e[0]) for e in R]; c = [q * e[1] for e in R]
    w = bfrt(A, c); y = [Fr(v, q) for v in w]
    assert all(sat(e, y) for e in S), 'pipeline solution violates S'
    assert max(abs(v) for v in y) <= 2 ** (n - 1)
    ratios.append(float(max(abs(v) for v in y)) / 2 ** (n - 1)); c3 += 1
OUT['pipeline_checks'] = c3; OUT['pipeline_max_ratio_to_2^(n-1)'] = max(ratios)

# 4. Smith transfer: G = (1/2)Z + (1/3)Z*sqrt2 ; elements (a,b) = a + b*sqrt2 ; G cap Q = (1/2)Z
def smith(A):
    """Return U,D,V integer with U A V = D diagonal (nonneg diag)."""
    m, n = len(A), len(A[0]); D = [r[:] for r in A]
    U = [[int(i == j) for j in range(m)] for i in range(m)]; V = [[int(i == j) for j in range(n)] for i in range(n)]
    def rowop(M, i, j, k): M[i] = [a + k * b for a, b in zip(M[i], M[j])]
    def colop(M, i, j, k):
        for r in M: r[i] += k * r[j]
    t = 0
    while t < min(m, n):
        piv = [(abs(D[i][j]), i, j) for i in range(t, m) for j in range(t, n) if D[i][j]]
        if not piv: break
        _, i, j = min(piv)
        D[t], D[i] = D[i], D[t]; U[t], U[i] = U[i], U[t]
        for M in (D, V):
            for r in M: r[t], r[j] = r[j], r[t]
        done = True
        for i in range(t + 1, m):
            k = D[i][t] // D[t][t]; rowop(D, i, t, -k); rowop(U, i, t, -k)
            if D[i][t]: done = False
        for j in range(t + 1, n):
            k = D[t][j] // D[t][t]; colop(D, j, t, -k); colop(V, j, t, -k)
            if D[t][j]: done = False
        if not done: continue
        bad = [(i, j) for i in range(t + 1, m) for j in range(t + 1, n) if D[i][j] % D[t][t]]
        if bad:
            i, _ = bad[0]; rowop(D, t, i, 1); rowop(U, t, i, 1); continue
        if D[t][t] < 0:
            D[t] = [-a for a in D[t]]; U[t] = [-a for a in U[t]]
        t += 1
    return U, D, V

def inv_unimod(V):
    n = len(V); aug = [[Fr(x) for x in V[r]] + [Fr(int(r == s)) for s in range(n)] for r in range(n)]
    for col in range(n):
        p = next(r for r in range(col, n) if aug[r][col] != 0); aug[col], aug[p] = aug[p], aug[col]
        pv = aug[col][col]; aug[col] = [v / pv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col]:
                f = aug[r][col]; aug[r] = [a - f * b for a, b in zip(aug[r], aug[col])]
    W = [[aug[r][n + s] for s in range(n)] for r in range(n)]
    assert all(v.denominator == 1 for row in W for v in row); return [[int(v) for v in row] for row in W]

c4 = 0
for _ in range(400):
    n = random.randint(1, 5)
    E = all_eqs(n)
    # random G-point: rational part in (1/2)Z with x1=1-ish, irrational part in (1/3)Z, then constrain S to equations it satisfies
    a = [Fr(random.randint(-8, 8), 2) for _ in range(n)]; a[0] = Fr(1)
    bvec = [Fr(random.choice([0, 0, random.randint(-6, 6)]), 3) for _ in range(n)]; bvec[0] = Fr(0)
    S = [e for e in E if sum(r * u for r, u in zip(e[0], a)) == e[1] and sum(r * u for r, u in zip(e[0], bvec)) == 0]
    S = random.sample(S, min(len(S), random.randint(1, 3 * n)))
    A = [list(e[0]) for e in S]; rhs = [e[1] for e in S]
    U, D, V = smith(A)
    assert [[sum(U[i][k] * sum(A[k][l] * V[l][j] for l in range(n)) for k in range(len(A))) for j in range(n)] for i in range(len(A))] == D
    Vi = inv_unimod(V)
    za = [sum(Vi[i][j] * a[j] for j in range(n)) for i in range(n)]
    zb = [sum(Vi[i][j] * bvec[j] for j in range(n)) for i in range(n)]
    Ub = [sum(U[i][k] * rhs[k] for k in range(len(A))) for i in range(len(A))]
    r = sum(1 for i in range(min(len(A), n)) if D[i][i])
    for i in range(r):
        assert zb[i] == 0 and za[i] == Fr(Ub[i], D[i][i]) and (2 * za[i]).denominator == 1  # forced coords rational, in (1/2)Z
    assert all(Ub[i] == 0 for i in range(r, len(A)))
    zp = [za[i] if i < r else Fr(0) for i in range(n)]
    xp = [sum(V[i][j] * zp[j] for j in range(n)) for i in range(n)]
    assert all(sat(e, xp) for e in S) and all((2 * v).denominator == 1 for v in xp); c4 += 1
OUT['smith_transfer_checks'] = c4

# 5. sharpness: doubling chain has unique solution with max 2^(n-1); Route-B obstruction example
for n in range(1, 8):
    S = [((1,) + (0,) * (n - 1), 1)]
    for i in range(n - 1):
        r = [0] * n; r[i] = 2; r[i + 1] = -1; S.append((tuple(r), 0))
    assert rank([list(e[0]) for e in S]) == n
OUT['doubling_chain_full_rank_n1..7'] = True
# x1=1, x2+x2=x3, x3+x1=x4 over Z: x4=2x2+1 is odd, so {x4=0} has no Z-point though a Q-point exists.
OUT['routeB_parity_obstruction'] = 'x4=2*x2+1: x4=0 forces x2=-1/2 not in Z; Q-feasible, Z-infeasible'
OUT['status'] = 'all assertions passed; finite controls, not a proof'
json.dump(OUT, open(sys.argv[1], 'w'), indent=1, sort_keys=True)
print(json.dumps(OUT, sort_keys=True))
