"""Exact spectral structure of the (poset-correct) I2 on the symmetric subspace S_n, n = 1..NMAX.
Basis of S_n (flag-f coordinates): e_T + e_{T*} over reversal-orbit representatives T.
Exact characteristic polynomial (Faddeev-LeVerrier over Fractions), rational roots, algebraic vs
geometric multiplicities (exact ranks).  Usage: hetyei_spec.py NMAX SCRIPTDIR"""
import sys, importlib.util
from fractions import Fraction
SD = sys.argv[-1]
spec = importlib.util.spec_from_file_location('h2', SD + '/hetyei_I2.py'); h2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(h2)
NMAX = int(sys.argv[1])
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
    n = len(A); I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    Mk = [[Fraction(0)] * n for _ in range(n)]; c = [Fraction(1)]
    for k in range(1, n + 1):
        # M_k = A M_{k-1} + c_{k-1} I ;  c_k = -tr(A M_k)/k
        AM = [[sum(A[i][t] * Mk[t][j] for t in range(n) if A[i][t]) for j in range(n)] for i in range(n)]
        Mk = [[AM[i][j] + (c[-1] if i == j else 0) for j in range(n)] for i in range(n)]
        AMk = [[sum(A[i][t] * Mk[t][j] for t in range(n) if A[i][t]) for j in range(n)] for i in range(n)]
        c.append(-sum(AMk[i][i] for i in range(n)) / k)
    return c  # x^n + c1 x^{n-1} + ... + cn
def peval(c, x):
    v = Fraction(0)
    for a in c: v = v * x + a
    return v
def pdiv_root(c, r):
    out = [c[0]]
    for a in c[1:-1]: out.append(a + out[-1] * r)
    return out
for n in range(1, NMAX + 1):
    N = 1 << n
    rev = lambda m: h2.tomask([n + 1 - i for i in h2.bits(m, n)])
    reps = sorted({min(m, rev(m)) for m in range(N)}); pos = {T: i for i, T in enumerate(reps)}
    d = len(reps)
    A = [[Fraction(0)] * d for _ in range(d)]  # column j = image of basis j in rep coordinates
    sym_ok = True
    for j, T in enumerate(reps):
        img = dict(h2.I2_column(T, n))
        if rev(T) != T:
            for m, c in h2.I2_column(rev(T), n).items(): img[m] = img.get(m, 0) + c
        for m, c in img.items():
            if img.get(rev(m), 0) != c: sym_ok = False
        for m, c in img.items():
            if m == min(m, rev(m)): A[pos[m]][j] += c
    cp = charpoly(A) if d <= 40 else None
    roots = {}
    if cp is not None:
        c = cp[:]
        cands = [Fraction(0)] + [Fraction(2 ** k) for k in range(0, 2 * n + 4)] + [Fraction(-2 ** k) for k in range(0, 2 * n + 4)]
        for r in cands:
            while len(c) > 1 and peval(c, r) == 0:
                roots[r] = roots.get(r, 0) + 1; c = pdiv_root(c, r)
        rest_deg = len(c) - 1
    else:
        rest_deg = None
        cands = [Fraction(0)] + [Fraction(2 ** k) for k in range(0, 2 * n + 4)]
    geo = {}
    for r in (roots if cp is not None else cands):
        g = d - rank([[A[i][j] - (r if i == j else 0) for j in range(d)] for i in range(d)])
        if g: geo[r] = g
    print('n', n, 'dim S_n', d, 'image symmetric', sym_ok,
          'alg mult', {str(k): v for k, v in sorted(roots.items())} if cp is not None else 'skipped',
          'non-rational-root degree', rest_deg,
          'geo mult', {str(k): v for k, v in sorted(geo.items())}, 'sum geo', sum(geo.values()), flush=True)
