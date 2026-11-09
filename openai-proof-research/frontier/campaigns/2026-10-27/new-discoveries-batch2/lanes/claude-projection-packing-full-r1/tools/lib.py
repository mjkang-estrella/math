"""Exploratory numerics (float, via lp_solve). Support evidence only; never a proof.
V = F R^n inside l_inf^N, F an N x n matrix whose rows phi_j are the coordinate functionals."""
import itertools, math, os, random, subprocess, tempfile

TMP = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tmp')
os.makedirs(TMP, exist_ok=True)


def lp(obj, cons, nvars, maximize=False):
    """obj: dict var->coef; cons: list of (dict, op, rhs). All vars free. Returns (value, x)."""
    name = lambda i: 'v%d' % i
    def expr(d):
        s = ' '.join('%+.15g %s' % (c, name(i)) for i, c in d.items() if abs(c) > 1e-13)
        return s if s else '0 v0'
    lines = [('max: ' if maximize else 'min: ') + expr(obj) + ';']
    for k, (d, op, r) in enumerate(cons):
        lines.append('c%d: %s %s %.15g;' % (k, expr(d), op, 0.0 if abs(r) < 1e-13 else r))
    lines.append('free ' + ', '.join(name(i) for i in range(nvars)) + ';')
    fd, path = tempfile.mkstemp(suffix='.lp', dir=TMP)
    with os.fdopen(fd, 'w') as f:
        f.write('\n'.join(lines) + '\n')
    try:
        for opts in (['-e', '1e-11'], ['-s4', '-e', '1e-9'], ['-piv0', '-s4', '-e', '1e-8'], ['-piv1', '-e', '1e-7']):
            out = subprocess.run(['lp_solve', '-S4'] + opts + [path], capture_output=True, text=True).stdout
            if 'Value of objective function' in out: break
    finally:
        os.remove(path)
    if 'infeasible' in out or 'unbounded' in out:
        return None, None
    if 'Value of objective function' not in out:
        raise RuntimeError('lp_solve failed: ' + out[:300])
    val = float(out.split('Value of objective function:')[1].split()[0])
    x = [0.0] * nvars
    body = out.split('Actual values of the variables:')[1].split('Actual values of the constraints:')[0]
    for ln in body.strip().splitlines():
        a, b = ln.split()
        x[int(a[1:])] = float(b)
    return val, x


def mat_mul(a, b):
    return [[sum(x * y for x, y in zip(r, c)) for c in zip(*b)] for r in a]


def row_norm(p):
    return max(sum(abs(x) for x in r) for r in p)


def projection_constant(F):
    """min ||F A||_inf over A (n x N) with A F = I. Returns (lambda, P)."""
    N, n = len(F), len(F[0])
    a = lambda i, j: i * N + j            # A[i][j]
    z = lambda l, j: n * N + l * N + j    # |P[l][j]| bound
    t = n * N + N * N
    cons = []
    for i in range(n):
        for k in range(n):
            cons.append(({a(i, j): F[j][k] for j in range(N)}, '=', 1.0 if i == k else 0.0))
    for l in range(N):
        for j in range(N):
            e = {a(i, j): F[l][i] for i in range(n)}
            e1 = dict(e); e1[z(l, j)] = -1.0; cons.append((e1, '<=', 0.0))
            e2 = {k: -v for k, v in e.items()}; e2[z(l, j)] = -1.0; cons.append((e2, '<=', 0.0))
        d = {z(l, j): 1.0 for j in range(N)}; d[t] = -1.0; cons.append((d, '<=', 0.0))
    val, x = lp({t: 1.0}, cons, t + 1)
    A = [[x[a(i, j)] for j in range(N)] for i in range(n)]
    return val, mat_mul(F, A)


def fractional_value(P, K):
    """max t: exists w>=0, sum_i w_ij<=1, sum_j |p_{k_i j}| w_ij >= t for all i."""
    N, n = len(P), len(K)
    w = lambda i, j: i * N + j
    t = n * N
    cons = []
    for j in range(N):
        cons.append(({w(i, j): 1.0 for i in range(n)}, '<=', 1.0))
    for i in range(n):
        for j in range(N):
            cons.append(({w(i, j): 1.0}, '>=', 0.0))
        d = {w(i, j): abs(P[K[i]][j]) for j in range(N)}; d[t] = -1.0
        cons.append((d, '>=', 0.0))
    val, x = lp({t: 1.0}, cons, t + 1, maximize=True)
    return val


def best_fractional(P, n):
    N = len(P); best = (-1, None)
    for K in itertools.combinations(range(N), n):
        v = fractional_value(P, list(K))
        if v is not None and v > best[0]:
            best = (v, K)
    return best


def integral_packing(P, n, thr):
    """Max number of disjoint good sets (exact enumeration of inclusion-minimal good sets)."""
    N = len(P); good = []
    for mask in range(1, 1 << N):
        idx = [j for j in range(N) if mask >> j & 1]
        if any(sum(abs(P[k][j]) for j in idx) >= thr - 1e-12 for k in idx):
            good.append(mask)
    mins = [a for a in good if not any(b != a and b & a == b for b in good)]
    best = 0
    def rec(start, used, cnt):
        nonlocal best
        best = max(best, cnt)
        if best >= n: return
        for i in range(start, len(mins)):
            if not mins[i] & used: rec(i + 1, used | mins[i], cnt + 1)
    rec(0, 0, 0)
    return best


# ---- Banach-Mazur distance to l_inf^2 for two-dimensional V (n = 2) ----
def ball_vertices(F):
    vs = []
    for (j, k) in itertools.combinations(range(len(F)), 2):
        a, b = F[j], F[k]; det = a[0] * b[1] - a[1] * b[0]
        if abs(det) < 1e-14: continue
        for s in (1, -1):
            for r in (1, -1):
                x = ((s * b[1] - r * a[1]) / det, (r * a[0] - s * b[0]) / det)
                if all(abs(f[0] * x[0] + f[1] * x[1]) <= 1 + 1e-10 for f in F): vs.append(x)
    return vs


def dist_given(F, verts, g):
    """g = (g1, g2) columns of T^{-1}: l_inf^2 -> V. Returns ||T|| ||T^{-1}||."""
    (a, b), (c, d) = g
    det = a * d - b * c
    if abs(det) < 1e-12: return float('inf')
    tinv = max(abs(f[0] * a + f[1] * b) + abs(f[0] * c + f[1] * d) for f in F)
    t1 = (d / det, -c / det); t2 = (-b / det, a / det)   # rows of T
    tn = max(max(abs(t1[0] * x + t1[1] * y), abs(t2[0] * x + t2[1] * y)) for x, y in verts)
    return tn * tinv


def bm_distance_2d(F, rng, restarts=60, iters=400):
    verts = ball_vertices(F)
    best = float('inf'); arg = None
    # coarse grid on angles (scale of each column is irrelevant up to the ratio)
    for _ in range(restarts):
        th1, th2, r = rng.uniform(0, math.pi), rng.uniform(0, math.pi), math.exp(rng.uniform(-1, 1))
        cur = (th1, th2, r)
        f = lambda s: dist_given(F, verts, ((math.cos(s[0]), math.sin(s[0])), (s[2] * math.cos(s[1]), s[2] * math.sin(s[1]))))
        val = f(cur); step = 0.3
        for _ in range(iters):
            cand = (cur[0] + rng.gauss(0, step), cur[1] + rng.gauss(0, step), cur[2] * math.exp(rng.gauss(0, step)))
            v = f(cand)
            if v < val: cur, val = cand, v
            else: step *= 0.985
            if step < 1e-7: break
        if val < best: best, arg = val, cur
    return best, arg
