"""Corrected spectral analysis for Hetyei Conjecture 40 (347231) with the poset-correct I2 (flag-f basis).
Facts used: I2(u*) = I2(u) (equivalent to Corollary 33), so I2 = I2 o pi with pi = symmetrisation.
 * B = pi o I2 restricted to S_n (d x d); nonzero eigenvalues/Jordan data of I2 on V equal those of B.
 * For each eigenvalue lam of I2 (roots of charpoly of B, plus 0), E_lam = dim( ker(I2 - lam) cap S_n ),
   computed exactly as nullity of the 2^n x d matrix (I2 - lam) restricted to S_n.
 * If sum_lam E_lam < d = dim S_n, then S_n has NO generating set consisting of I2-eigenvectors.
Also verifies I2(u*) == I2(u) on all basis vectors.  Usage: hetyei_spec2.py NMIN NMAX SCRIPTDIR"""
import sys, importlib.util
from fractions import Fraction
SD = sys.argv[-1]
spec = importlib.util.spec_from_file_location('h2', SD + '/hetyei_I2.py'); h2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(h2)
NMIN, NMAX = int(sys.argv[1]), int(sys.argv[2])
def rank(Mx):
    A = [row[:] for row in Mx]; r = 0; m = len(A); n = len(A[0]) if A else 0
    for c in range(n):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][c]
        for i in range(r + 1, m):
            if A[i][c] != 0:
                f = A[i][c] / pv; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        r += 1
    return r
def charpoly(A):
    n = len(A); Mk = [[Fraction(0)] * n for _ in range(n)]; c = [Fraction(1)]
    for k in range(1, n + 1):
        AM = [[sum(A[i][t] * Mk[t][j] for t in range(n) if A[i][t]) for j in range(n)] for i in range(n)]
        Mk = [[AM[i][j] + (c[-1] if i == j else 0) for j in range(n)] for i in range(n)]
        AMk = [[sum(A[i][t] * Mk[t][j] for t in range(n) if A[i][t]) for j in range(n)] for i in range(n)]
        c.append(-sum(AMk[i][i] for i in range(n)) / k)
    return c
def peval(c, x):
    v = Fraction(0)
    for a in c: v = v * x + a
    return v
def pdiv_root(c, r):
    out = [c[0]]
    for a in c[1:-1]: out.append(a + out[-1] * r)
    return out
for n in range(NMIN, NMAX + 1):
    N = 1 << n
    rev = lambda m: h2.tomask([n + 1 - i for i in h2.bits(m, n)])
    cols = {T: h2.I2_column(T, n) for T in range(N)}
    star_ok = all({k: v for k, v in cols[T].items() if v} == {k: v for k, v in cols[rev(T)].items() if v} for T in range(N))
    reps = sorted({min(m, rev(m)) for m in range(N)}); pos = {T: i for i, T in enumerate(reps)}; d = len(reps)
    def symvec(T):  # basis vector of S_n as dict
        return {T: 1} if rev(T) == T else {T: 1, rev(T): 1}
    def I2vec(v):
        out = {}
        for T, c in v.items():
            for m, x in cols[T].items(): out[m] = out.get(m, 0) + c * x
        return out
    # B = pi o I2 on S_n in basis symvec(T): pi(w) coefficient on symvec(R) = (w[R]+w[R*])/2 (R != R*), w[R] (R = R*)
    B = [[Fraction(0)] * d for _ in range(d)]
    imgs = []
    for j, T in enumerate(reps):
        w = I2vec(symvec(T)); imgs.append(w)
        for R in reps:
            val = Fraction(w.get(R, 0)) if rev(R) == R else Fraction(w.get(R, 0) + w.get(rev(R), 0), 2)
            B[pos[R]][j] = val
    cp = charpoly(B); c = cp[:]; roots = {}
    for r in [Fraction(0)] + [Fraction(s * 2 ** k) for k in range(0, 2 * n + 6) for s in (1, -1)]:
        while len(c) > 1 and peval(c, r) == 0:
            roots[r] = roots.get(r, 0) + 1; c = pdiv_root(c, r)
    lams = sorted(set(roots) | {Fraction(0)})
    E = {}
    for lam in lams:
        # columns: (I2 - lam) applied to symvec(T), as 2^n-vectors
        Mx = []
        for j, T in enumerate(reps):
            w = dict(imgs[j])
            for m, x in symvec(T).items(): w[m] = w.get(m, 0) - lam * x
            Mx.append([Fraction(w.get(m, 0)) for m in range(N)])
        # nullity of the map R^d -> R^N whose columns are Mx rows
        E[lam] = d - rank(Mx)
    tot = sum(E.values())
    print('n', n, 'dim S_n', d, 'I2(u*)==I2(u):', star_ok, '| charpoly(B) rational roots (alg mult):',
          {str(k): v for k, v in roots.items()}, 'irrational-part degree', len(c) - 1,
          '| dim(eigvecs in S_n) per eigenvalue', {str(k): v for k, v in E.items() if v}, 'total', tot,
          'SPANS S_n' if tot >= d else 'DOES NOT SPAN S_n', flush=True)
