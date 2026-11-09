# Annealing for counterexamples to Conjecture 4.12 of arXiv:2508.01163 (MathDB 369616) on connected
# graphs with n vertices and m edges (n <= m <= 2n-2 is the open range).  Objective (maximize):
# excess = #{theta>2} - #{theta<2} - (m-n+1) for signless Laplacian eigenvalues theta, plus a tie-breaker
# in (0,0.5) rewarding a sub-2 eigenvalue close to 2.  excess > 0 is a counterexample.
import sys, json, numpy as np
n, m, iters, seed, restarts = map(int, sys.argv[1:6]); rng = np.random.default_rng(seed); EPS = 1e-7
c = m - n + 1

def connected(A):
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for v in np.nonzero(A[u])[0]:
            if v not in seen: seen.add(int(v)); st.append(int(v))
    return len(seen) == n

def f(A):
    th = np.linalg.eigvalsh(np.diag(A.sum(1)) + A)
    ex = int((th > 2 + EPS).sum() - (th < 2 - EPS).sum() - c)
    below = th[th < 2 - EPS]
    tb = 0.5 * np.exp(-(2 - below.max()) / 0.05) if len(below) else 0
    return ex + tb, ex

best = (-99, None)
for r in range(restarts):
    A = np.zeros((n, n))
    for v in range(1, n):
        u = int(rng.integers(0, v)); A[u, v] = A[v, u] = 1
    while A.sum() / 2 < m:
        u, v = rng.integers(0, n, 2)
        if u != v: A[u, v] = A[v, u] = 1
    cur, ex = f(A); T = 0.3
    for it in range(iters):
        E = np.argwhere(np.triu(A)); N = np.argwhere(np.triu(1 - A, 1))
        a = E[rng.integers(len(E))]; b = N[rng.integers(len(N))]
        A[a[0], a[1]] = A[a[1], a[0]] = 0; A[b[0], b[1]] = A[b[1], b[0]] = 1
        ok = connected(A)
        if ok:
            s, e2 = f(A)
            if s >= cur or rng.random() < np.exp((s - cur) / T): cur, ex = s, e2
            else: ok = False
        if not ok: A[a[0], a[1]] = A[a[1], a[0]] = 1; A[b[0], b[1]] = A[b[1], b[0]] = 0
        T = max(T * 0.999, 0.01)
        if ex > best[0]: best = (ex, np.argwhere(np.triu(A)).tolist())
        if ex > 0: break
    if best[0] > 0: break
print(json.dumps(dict(n=n, m=m, max_excess=best[0], edges=best[1])))
