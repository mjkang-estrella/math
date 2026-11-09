# All triangulations of a convex n-gon (= all labelled maximal outerplanar graphs with the boundary
# cycle 0..n-1; every maximal outerplanar graph on n >= 3 vertices arises), checking
# Conjecture 9.5(ii) of arXiv:2506.07264 (MathDB 368745): s+(G) >= 2n for n >= 8.
import sys, json, numpy as np
from functools import lru_cache
sys.setrecursionlimit(10000)

@lru_cache(None)
def tri(i, j):
    # list of diagonal tuples triangulating polygon i..j (edge i-j is a side)
    if j - i < 2: return [()]
    out = []
    for k in range(i + 1, j):
        for a in tri(i, k):
            for b in tri(k, j):
                d = a + b + (((i, k),) if k - i > 1 else ()) + (((k, j),) if j - k > 1 else ())
                out.append(d)
    return out

res = {}
for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    T = tri(0, n - 1); best = (1e9, None); cnt = 0
    for s in range(0, len(T), 20000):
        chunk = T[s:s + 20000]; A = np.zeros((len(chunk), n, n))
        for v in range(n): A[:, v, (v + 1) % n] = A[:, (v + 1) % n, v] = 1
        for t, d in enumerate(chunk):
            for u, v in d: A[t, u, v] = A[t, v, u] = 1
        ev = np.linalg.eigvalsh(A); sp = (np.where(ev > 0, ev, 0) ** 2).sum(axis=1) - 2 * n
        j = int(np.argmin(sp)); cnt += len(chunk)
        if sp[j] < best[0]: best = (float(sp[j]), chunk[j])
    tri.cache_clear() if n > 14 else None
    res[n] = dict(triangulations=cnt, min_splus_minus_2n=best[0], argmin_diagonals=best[1])
    print(n, cnt, round(best[0], 6), best[1], flush=True)
json.dump(res, open(sys.argv[3], 'w'), indent=1)
