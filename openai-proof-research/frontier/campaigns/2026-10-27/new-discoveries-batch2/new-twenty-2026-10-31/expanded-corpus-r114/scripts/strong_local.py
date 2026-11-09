# Simulated annealing over connected graphs with n vertices and m = n - 1 + c edges, minimizing
# s+(G) - n (Conjecture 1.2 of arXiv:2506.07264, MathDB 368742; a negative value is a counterexample).
# Moves: delete one edge and insert one non-edge, rejecting disconnected results.
import sys, json, numpy as np
n = int(sys.argv[1]); c = int(sys.argv[2]); iters = int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]))
restarts = int(sys.argv[5]) if len(sys.argv) > 5 else 3
m = n - 1 + c

def connected(A):
    seen = {0}; st = [0]
    while st:
        u = st.pop()
        for v in np.nonzero(A[u])[0]:
            if v not in seen: seen.add(int(v)); st.append(int(v))
    return len(seen) == n

def score(A):
    ev = np.linalg.eigvalsh(A); return float((ev[ev > 0] ** 2).sum() - n)

best = (1e9, None)
for r in range(restarts):
    A = np.zeros((n, n))
    for v in range(1, n):
        u = int(rng.integers(0, v)); A[u, v] = A[v, u] = 1
    while A.sum() / 2 < m:
        u, v = rng.integers(0, n, 2)
        if u != v: A[u, v] = A[v, u] = 1
    cur = score(A); T = 0.05
    for it in range(iters):
        E = np.argwhere(np.triu(A)); N = np.argwhere(np.triu(1 - A, 1))
        a = E[rng.integers(len(E))]; b = N[rng.integers(len(N))]
        A[a[0], a[1]] = A[a[1], a[0]] = 0; A[b[0], b[1]] = A[b[1], b[0]] = 1
        if connected(A):
            s = score(A)
            if s <= cur or rng.random() < np.exp((cur - s) / T): cur = s
            else: A[a[0], a[1]] = A[a[1], a[0]] = 1; A[b[0], b[1]] = A[b[1], b[0]] = 0
        else: A[a[0], a[1]] = A[a[1], a[0]] = 1; A[b[0], b[1]] = A[b[1], b[0]] = 0
        T = max(T * 0.9993, 1e-4)
        if cur < best[0]: best = (cur, np.argwhere(np.triu(A)).tolist())
print(json.dumps(dict(n=n, c=c, min_splus_minus_n=best[0], edges=best[1])))
