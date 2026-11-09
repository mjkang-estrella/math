"""371239 diagnostic in G = Z_N^d (small). For supports E (containing 0, |E| <= emax) and
1-dim kernels f of character submatrices M[T,E] (|T| = |E|-1), compute Sigma = supp fhat
(float, tol 1e-9) and the ratio |supp f|^{k+1} Q_k(Sigma) / |G|^{k+1}; report minimum per k.
Diagnostic only (floating zero test); any failure is re-verified exactly elsewhere.
usage: gowers_general.py N d emax kmax
"""
import sys, itertools, cmath
from functools import lru_cache
N, d, emax, kmax = map(int, sys.argv[1:5])
G = list(itertools.product(range(N), repeat=d))
idx = {g: i for i, g in enumerate(G)}
n = len(G)
add = [[idx[tuple((a + b) % N for a, b in zip(G[i], G[j]))] for j in range(n)] for i in range(n)]
neg = [idx[tuple((-a) % N for a in g)] for g in G]
CH = [[cmath.exp(-2j * cmath.pi * sum(a * b for a, b in zip(m, x)) / N) for x in G] for m in G]

def det(M):
    M = [row[:] for row in M]; m = len(M); D = 1
    for c in range(m):
        piv = max(range(c, m), key=lambda r: abs(M[r][c]))
        if abs(M[piv][c]) < 1e-12:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]; D = -D
        D *= M[c][c]
        for r in range(c + 1, m):
            t = M[r][c] / M[c][c]
            for cc in range(c, m):
                M[r][cc] -= t * M[c][cc]
    return D

def kernel(T, E):  # cofactor vector of (e-1) x e matrix
    M = [[CH[t][x] for x in E] for t in T]
    if len(T) == 0:
        return [1]
    return [(-1) ** j * det([row[:j] + row[j + 1:] for row in M]) for j in range(len(E))]

def minus(A, h):  # A - h as bitmask
    B = 0
    for i in range(n):
        if A >> i & 1:
            B |= 1 << add[i][neg[h]]
    return B

@lru_cache(maxsize=None)
def Q(A, k):
    if k == 0:
        return bin(A).count('1')
    return sum(Q(A & minus(A, h), k - 1) for h in range(n))

best = {k: (9e9, None) for k in range(2, kmax + 1)}
seen = set()
for e in range(2, emax + 1):
    for Erest in itertools.combinations(range(1, n), e - 1):
        E = (0,) + Erest
        for T in itertools.combinations(range(n), e - 1):
            f = kernel(T, E)
            nf = max(abs(c) for c in f)
            if nf < 1e-9:
                continue
            f = [c / nf for c in f]
            fh = [sum(CH[m][x] * c for x, c in zip(E, f)) for m in range(n)]
            Sig = 0
            for i in range(n):
                if abs(fh[i]) > 1e-9:
                    Sig |= 1 << i
            es = sum(1 for c in f if abs(c) > 1e-9)
            key = (es, Sig)
            if key in seen:
                continue
            seen.add(key)
            for k in range(2, kmax + 1):
                r = es ** (k + 1) * Q(Sig, k) / n ** (k + 1)
                if r < best[k][0]:
                    best[k] = (r, (es, [G[i] for i in range(n) if Sig >> i & 1], [G[i] for i in E], Q(Sig, k)))
for k in range(2, kmax + 1):
    r, w = best[k]
    print(f'N={N} d={d} |G|={n} k={k} min ratio={r:.6f}', 'FAIL' if r < 1 - 1e-12 else 'ok', w if r < 1 - 1e-12 else (w[0], len(w[1])) if w else None)
print('patterns', len(seen))
