"""Experiment for MathDB 342653: do extremal t-degrees of unreduced Burau matrix entries of an e-homogeneous braid word
equal block letter counts?  Random e-homogeneous words (all generators used); for each entry (i,j) record
(maxdeg, mindeg) and test candidate formulas against block-count vectors.
Usage: burau_blocks.py e trials maxlen seed
"""
import sys, random
es = sys.argv[1]; trials = int(sys.argv[2]); maxlen = int(sys.argv[3]); random.seed(int(sys.argv[4]))
e = [1 if c == '+' else -1 for c in es]; m = len(e); n = m + 1
blk = []; b = 0
for i in range(m):
    if i and e[i] != e[i - 1]: b += 1
    blk.append(b)
nb = b + 1

def padd(p, q, s=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + s * v
        if r[k] == 0: del r[k]
    return r
def pmul(p, q):
    r = {}
    for a, x in p.items():
        for c, y in q.items():
            r[a + c] = r.get(a + c, 0) + x * y
    return {k: v for k, v in r.items() if v}

def gen(i, s):
    # unreduced Burau, acting on rows: identity except 2x2 block at (i-1,i)
    M = [[({0: 1} if a == c else {}) for c in range(n)] for a in range(n)]
    a = i - 1
    if s == 1:
        M[a][a] = {0: 1, 1: -1}; M[a][a + 1] = {1: 1}; M[a + 1][a] = {0: 1}; M[a + 1][a + 1] = {}
    else:
        M[a][a] = {}; M[a][a + 1] = {0: 1}; M[a + 1][a] = {-1: 1}; M[a + 1][a + 1] = {0: 1, -1: -1}
    return M
def mmul(A, B):
    return [[ (lambda r, c: __import__('functools').reduce(lambda x, y: padd(x, y), [pmul(A[r][k], B[k][c]) for k in range(n)], {}))(r, c) for c in range(n)] for r in range(n)]

G = {(i, s): gen(i, s) for i in range(1, n) for s in (1, -1)}
rows = []
for tr in range(trials):
    L = random.randint(m, maxlen)
    w = list(range(1, n)) + [random.randint(1, m) for _ in range(L - m)]
    random.shuffle(w)
    M = [[({0: 1} if a == c else {}) for c in range(n)] for a in range(n)]
    for i in w: M = mmul(M, G[(i, e[i - 1])])
    cnt = [0] * nb
    for i in w: cnt[blk[i - 1]] += 1
    deg = [[(max(M[a][c]) if M[a][c] else None, min(M[a][c]) if M[a][c] else None) for c in range(n)] for a in range(n)]
    rows.append((cnt, deg, w))
# test: for each entry and each of max/min, is it a function of counts? and is it determined linearly?
print('e', es, 'blocks', blk, 'trials', trials)
for a in range(n):
    for c in range(n):
        for which in (0, 1):
            vals = [(tuple(r[0]), r[1][a][c][which]) for r in rows]
            # check if equals +-count of a single block
            for k in range(nb):
                for sgn in (1, -1):
                    if all(v is not None and v == sgn * cnt[k] for cnt, v in vals):
                        print(f'entry ({a},{c}) {"max" if which==0 else "min"}deg == {sgn}*c_{k}')
# affine fit: value = sum_k alpha_k c_k + beta over all samples (exact rational solve on first independent samples)
from fractions import Fraction
def fit(vals):
    pts = [(list(c) + [1], v) for c, v in vals if v is not None]
    if len(pts) < len(vals): return None
    # gaussian elimination least set
    k = nb + 1; A = []; y = []
    for x, v in pts:
        A.append([Fraction(t) for t in x]); y.append(Fraction(v))
    # normal equations
    N = [[sum(A[r][i] * A[r][j] for r in range(len(A))) for j in range(k)] for i in range(k)]
    Y = [sum(A[r][i] * y[r] for r in range(len(A))) for i in range(k)]
    for i in range(k):
        p = next((r for r in range(i, k) if N[r][i] != 0), None)
        if p is None: return None
        N[i], N[p] = N[p], N[i]; Y[i], Y[p] = Y[p], Y[i]
        for r in range(k):
            if r != i and N[r][i] != 0:
                f = N[r][i] / N[i][i]
                N[r] = [N[r][j] - f * N[i][j] for j in range(k)]; Y[r] -= f * Y[i]
    coef = [Y[i] / N[i][i] for i in range(k)]
    if all(sum(coef[j] * x[j] for j in range(k)) == v for x, v in zip(A, y)): return coef
    return None
for a in range(n):
    for c in range(n):
        for which in (0, 1):
            vals = [(tuple(r[0]), r[1][a][c][which]) for r in rows]
            cf = fit(vals)
            if cf is not None: print(f'entry ({a},{c}) {"max" if which==0 else "min"}deg = ' + ' + '.join(f'{x}*c{j}' for j, x in enumerate(cf[:-1])) + f' + {cf[-1]}')
import itertools
def det(Mx):
    k = len(Mx)
    if k == 0: return {0: 1}
    tot = {}
    for perm in itertools.permutations(range(k)):
        sgn = 1
        for i in range(k):
            for j in range(i + 1, k):
                if perm[i] > perm[j]: sgn = -sgn
        term = {0: sgn}
        for i in range(k):
            term = pmul(term, Mx[i][perm[i]])
            if not term: break
        if term: tot = padd(tot, term)
    return tot
print('--- contiguous principal minors')
store = {}
for cnt, deg, w in rows[:120]:
    M = [[({0: 1} if a == c else {}) for c in range(n)] for a in range(n)]
    for i in w: M = mmul(M, G[(i, e[i - 1])])
    for lo in range(n):
        for hi in range(lo + 1, n + 1):
            d = det([row[lo:hi] for row in M[lo:hi]])
            store.setdefault((lo, hi), []).append((tuple(cnt), (max(d) if d else None, min(d) if d else None)))
for key, lst in store.items():
    for which in (0, 1):
        cf = fit([(c, v[which]) for c, v in lst])
        if cf is not None: print(f'minor rows/cols {key} {"max" if which==0 else "min"}deg = ' + ' + '.join(f'{x}*c{j}' for j, x in enumerate(cf[:-1])) + f' + {cf[-1]}')
