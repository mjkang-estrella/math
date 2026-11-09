"""368807: per-tour non-adjacency directions for the n=8 vertex x* (exact rational linear algebra via sympy).
For tour T let K_T = {v : supp v in supp(x*) u T, row/col sums 0, flux_S v = 0 for x*-tight cuts S that T crosses once}.
x - T lies in K_T; we need v in K_T not parallel to x - T.  First try the T-independent space
W = {v : supp v in supp(x*), row/col sums 0}, then T-specific.
Writes outputs/asep/candidate/n8-certs.json with, per cyclic order L (0 first), an integer vector v (dict arc->int)."""
import sys, json, itertools
from fractions import Fraction
import sympy as sp
n = 8
X = [[Fraction(s) for s in r] for r in json.load(open('outputs/asep/candidate/n8-den4.json'))['X']]
cuts = [S for s in range(2, n - 1) for S in itertools.combinations(range(n), s)]
flux = lambda M, S: sum(M[i][j] for i in S for j in range(n) if j not in S)
tight = [S for S in cuts if flux(X, S) == 1]
supp = [(i, j) for i in range(n) for j in range(n) if X[i][j] != 0]
print('tight cuts', len(tight), 'support', len(supp))
def kernel(arcs, cutlist):
    rows = []
    for j in range(n): rows.append([1 if a[1] == j else 0 for a in arcs])
    for i in range(n): rows.append([1 if a[0] == i else 0 for a in arcs])
    for S in cutlist: rows.append([1 if (a[0] in S and a[1] not in S) else 0 for a in arcs])
    return sp.Matrix(rows).nullspace()
orders = [(0,) + p for p in itertools.permutations(range(1, n))]
certs = {}; patterns = {}; nW = 0
for L in orders:
    T = [[0] * n for _ in range(n)]
    for k in range(n): T[L[k]][L[(k + 1) % n]] = 1
    pat = tuple(k for k, S in enumerate(tight) if flux(T, S) == 1)
    arcsT = sorted(set(supp) | {(L[k], L[(k + 1) % n]) for k in range(n)})
    key = (pat, tuple(arcsT))
    d = [X[i][j] - T[i][j] for (i, j) in arcsT]
    if key not in patterns:
        patterns[key] = kernel(arcsT, [tight[k] for k in pat])
    basis = patterns[key]; chosen = None
    for b in basis:
        vec = [sp.nsimplify(c) for c in b]
        # not parallel to d
        par = all(vec[a] * d[b2] == vec[b2] * d[a] for a in range(len(d)) for b2 in range(len(d)))
        if not par:
            den = sp.ilcm(*[sp.fraction(c)[1] for c in vec]); iv = [int(c * den) for c in vec]
            g = 0
            for c in iv: g = sp.igcd(g, c)
            iv = [c // g for c in iv]; chosen = {f'{i},{j}': c for (i, j), c in zip(arcsT, iv) if c}; break
    if chosen is None: raise SystemExit(f'no certificate for {L}')
    certs[','.join(map(str, L))] = chosen
    if all(tuple(map(int, k.split(','))) in set(supp) for k in chosen): nW += 1
json.dump({'tight_cuts': [list(S) for S in tight], 'certs': certs}, open('outputs/asep/candidate/n8-certs.json', 'w'))
print('tours', len(certs), 'distinct (pattern,support) systems', len(patterns), 'certificates supported in supp(x*)', nW)
print('max |v|_1', max(sum(abs(c) for c in v.values()) for v in certs.values()), 'max support', max(len(v) for v in certs.values()))
