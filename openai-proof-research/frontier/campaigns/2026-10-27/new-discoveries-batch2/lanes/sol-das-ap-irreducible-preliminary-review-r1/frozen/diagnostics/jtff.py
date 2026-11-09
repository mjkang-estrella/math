"""Exact small-case check of Dwivedi-Blasiak-Grinberg, arXiv:2302.07239v2, Conjecture 3.3:
lambda = p-shifted n-staircase of length k (parts p+(k-1)n,...,p+n,p), k >= n+1, p > n:
P(det J_lambda(z) = 0) = 1 - prod_{i=1}^{n+1} (1 - q^{-i}),  z_1,z_2,... uniform in F_q,
z_0 = 1, z_i = 0 for i < 0.  Exhaustive count over F_q^{V}, q prime.  Exact integers."""
import sys, json, itertools
from fractions import Fraction
import numpy as np


def detzero_count(lam, q):
    k = len(lam)
    idx = [[lam[i] - i + j for j in range(k)] for i in range(k)]  # 0-based i,j: z_{lam_i - i + j}
    V = max(max(r) for r in idx)
    N = q ** V
    if N > 600_000:  # fixed 512 MiB cap
        return None, V
    Z = np.indices((q,) * V).reshape(V, -1).T.astype(np.int64)  # N x V, column t = z_{t+1}
    M = np.zeros((N, k, k), dtype=np.int64)
    for i in range(k):
        for j in range(k):
            t = idx[i][j]
            M[:, i, j] = Z[:, t - 1] if t >= 1 else (1 if t == 0 else 0)
    inv = [0] + [pow(a, q - 2, q) for a in range(1, q)]
    inv = np.array(inv, dtype=np.int64)
    singular = np.zeros(N, dtype=bool)
    for c in range(k):
        # pivot: first row r >= c with nonzero entry in column c
        col = M[:, c:, c] % q
        has = col != 0
        singular |= ~has.any(axis=1)
        piv = np.argmax(has, axis=1) + c
        rows = np.arange(N)
        tmp = M[rows, piv, :].copy(); M[rows, piv, :] = M[rows, c, :]; M[rows, c, :] = tmp
        pv = M[:, c, c] % q
        pinv = inv[pv]
        for r in range(c + 1, k):
            f = (M[:, r, c] * pinv) % q
            M[:, r, :] = (M[:, r, :] - f[:, None] * M[:, c, :]) % q
    return int(singular.sum()), V


out = []
for n in (1, 2, 3):
    for p in range(n + 1, n + 3):
        for k in range(n + 1, n + 4):
            lam = [p + (k - 1 - i) * n for i in range(k)]
            for q in (2, 3, 5):
                cnt, V = detzero_count(lam, q)
                if cnt is None:
                    continue
                pred = 1 - np.prod([Fraction(1) - Fraction(1, q ** i) for i in range(1, n + 2)])
                got = Fraction(cnt, q ** V)
                out.append({'n': n, 'p': p, 'k': k, 'lambda': lam, 'q': q, 'vars': V,
                            'P_zero': str(got), 'conjectured': str(pred), 'match': got == pred})
                print(json.dumps(out[-1]), flush=True)
print('ALL_MATCH', all(r['match'] for r in out), len(out))
