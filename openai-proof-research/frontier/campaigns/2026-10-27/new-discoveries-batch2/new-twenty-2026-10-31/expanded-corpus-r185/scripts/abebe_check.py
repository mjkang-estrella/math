"""Numerical sanity check (diagnostic only) for MathDB 343238 (Abebe Conjecture 3) and the bridge
   s_t(L^+_{r-1}) <= max_{|A|=(r+1)t} sum_{rho in A} deg(rho) <= r f_r + C(t+r, r+1)    (Lew 2025 Thm 1.3 + Lovasz-KK)
on random pure r-dimensional complexes. Eigenvalues by cyclic Jacobi on the facet-side Gram matrix d^T d (same nonzero spectrum).
Usage: abebe_check.py r nverts trials seed
"""
import sys, random, itertools, math
r, nv, trials, seed = map(int, sys.argv[1:5])
random.seed(seed)

def jacobi_eigs(A, tol=1e-10, maxsweep=60):
    n = len(A); A = [row[:] for row in A]
    for _ in range(maxsweep):
        off = sum(A[i][j] ** 2 for i in range(n) for j in range(n) if i != j)
        if off < tol: break
        for p in range(n - 1):
            for q in range(p + 1, n):
                if abs(A[p][q]) < 1e-14: continue
                th = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = (1 if th >= 0 else -1) / (abs(th) + math.sqrt(th * th + 1))
                c = 1 / math.sqrt(t * t + 1); s = t * c
                for k in range(n):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq
                for k in range(n):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk
    return sorted((A[i][i] for i in range(n)), reverse=True)

worst_abebe = -1e9; worst_lew = -1e9; checked = 0
allfacets = list(itertools.combinations(range(nv), r + 1))
for tr in range(trials):
    F = random.sample(allfacets, random.randint(1, min(len(allfacets), 26)))
    f = len(F)
    # Gram matrix M[s][t] = <d s, d t>: diag r+1; +-1 if share a ridge (sign from orientation)
    def bd(s):
        return {tuple(s[:i] + s[i + 1:]): (-1) ** i for i in range(len(s))}
    B = [bd(s) for s in F]
    M = [[sum(B[i][k] * B[j].get(k, 0) for k in B[i]) for j in range(f)] for i in range(f)]
    ev = jacobi_eigs(M)
    deg = {}
    for s in F:
        for rho in bd(s): deg[rho] = deg.get(rho, 0) + 1
    ridges = len(deg)  # ridges of the pure complex (others only add zero eigenvalues)
    dsorted = sorted(deg.values(), reverse=True)
    for t in range(1, f + 1):
        st = sum(ev[:t])
        abebe = r * f + math.comb(t + r, r + 1)
        worst_abebe = max(worst_abebe, st - abebe)
        if (r + 1) * t <= ridges:
            lew = sum(dsorted[:(r + 1) * t])
            worst_lew = max(worst_lew, st - lew)
            assert lew <= abebe, (F, t, lew, abebe)
    checked += 1
print('r', r, 'nverts', nv, 'trials', checked, 'max(s_t - AbebeRHS)', round(worst_abebe, 6), 'max(s_t - LewRHS)', round(worst_lew, 6))
