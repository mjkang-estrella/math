# Local search for unicyclic counterexamples to Conjecture 9.1 of arXiv:2506.07264 beyond n = 15.
# Graph = cycle C_k (vertices 0..k-1) plus a forest given by parent pointers for vertices k..n-1.
# Objective: signed margin want*D, D = sum(lam*|lam|)/2, want = +1 (k=3 mod 4) or -1 (k=1 mod 4).
# Moves: re-parent a random non-cycle vertex to a random earlier-or-later vertex keeping a forest.
import sys, json, numpy as np
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
k = int(sys.argv[1]); n = int(sys.argv[2]); iters = int(sys.argv[3])
want = 1 if k % 4 == 3 else -1

def adj(par):
    A = np.zeros((n, n))
    for j in range(k): A[j, (j + 1) % k] = A[(j + 1) % k, j] = 1
    for v in range(k, n): A[v, par[v]] = A[par[v], v] = 1
    return A

def score(par):
    ev = np.linalg.eigvalsh(adj(par)); return want * (ev * np.abs(ev)).sum() / 2

def is_forest(par):
    for v in range(k, n):
        seen = set(); u = v
        while u >= k:
            if u in seen: return False
            seen.add(u); u = par[u]
    return True

best_overall = (9, None)
for restart in range(10**9):
    par = {v: int(rng.integers(0, k)) for v in range(k, n)}
    cur = score(par); T = 0.002
    for it in range(iters):
        v = int(rng.integers(k, n)); old = par[v]; par[v] = int(rng.integers(0, n))
        if par[v] == v or not is_forest(par): par[v] = old; continue
        s = score(par)
        if s < cur or rng.random() < np.exp((cur - s) / T): cur = s
        else: par[v] = old
        T *= 0.999
        if cur < best_overall[0]: best_overall = (cur, dict(par))
        if cur <= 0: break
    if best_overall[0] <= 0 or restart >= int(sys.argv[5] if len(sys.argv) > 5 else 3): break
print(json.dumps(dict(k=k, n=n, best_signed_margin=best_overall[0], parent=best_overall[1])))
