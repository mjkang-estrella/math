"""Numerical search for weighted graphs violating Barrett-Evans-Hall-Kempton Conjecture 6
(MathDB 353252): x + y - 2xy/n >= 1 with x = lambda_2(G), y = lambda_2(G^c), weights in [0,1].
Pure python (Jacobi eigenvalues), random restarts + adaptive coordinate/perturbation descent.
Usage: spread_search.py n restarts iters seed"""
import sys, random, math
n, R, IT, seed = map(int, sys.argv[1:5])
rnd = random.Random(seed)
pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
def eig(M):
    A = [r[:] for r in M]; m = len(A)
    for sweep in range(60):
        off = sum(A[i][j] ** 2 for i in range(m) for j in range(i + 1, m))
        if off < 1e-22: break
        for p in range(m):
            for q in range(p + 1, m):
                if abs(A[p][q]) < 1e-15: continue
                th = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = (1 if th >= 0 else -1) / (abs(th) + math.sqrt(th * th + 1))
                c = 1 / math.sqrt(t * t + 1); s = t * c
                for k in range(m):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p] = c * akp - s * akq; A[k][q] = s * akp + c * akq
                for k in range(m):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k] = c * apk - s * aqk; A[q][k] = s * apk + c * aqk
    return sorted(A[i][i] for i in range(m))
def lap(w):
    L = [[0.0] * n for _ in range(n)]
    for (i, j), x in zip(pairs, w):
        L[i][j] -= x; L[j][i] -= x; L[i][i] += x; L[j][j] += x
    return L
def f(w):
    ev = eig(lap(w))
    x = ev[1]; y = n - ev[-1]
    return x + y - 2 * x * y / n, x, y
best = (9e9, None)
for r in range(R):
    w = [rnd.choice([0.0, 1.0, rnd.random()]) for _ in pairs]
    val = f(w)[0]; step = 0.3
    for it in range(IT):
        w2 = w[:]
        for _ in range(rnd.randint(1, 3)):
            k = rnd.randrange(len(w2))
            w2[k] = min(1.0, max(0.0, w2[k] + rnd.gauss(0, step)))
        v2 = f(w2)[0]
        if v2 < val:
            w, val = w2, v2
        else:
            step = max(1e-4, step * 0.995)
    if val < best[0]:
        best = (val, w[:])
    print('restart', r, 'value', round(val, 9), flush=True)
v, x, y = f(best[1])
print('BEST', v, 'x', x, 'y', y, 'weights', [round(t, 6) for t in best[1]])
