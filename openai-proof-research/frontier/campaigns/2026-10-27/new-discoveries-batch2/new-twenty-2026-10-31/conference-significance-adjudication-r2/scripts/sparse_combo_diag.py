# Diagnostic only: minimum Hamming weight over F_19 of nonzero combinations of at most 3 rows
# of W20 (from the frozen certificate) and of the bordered Paley conference matrix of order 20.
import json, sys, itertools
p = 19
W = json.load(open(sys.argv[1]))["W"]
n = len(W)
def paley():
    chi = lambda a: 0 if a % p == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)
    M = [[0]*n for _ in range(n)]
    for j in range(1, n): M[0][j] = 1; M[j][0] = -1
    for i in range(p):
        for j in range(p): M[i+1][j+1] = chi(j - i)
    return M
def check(M):
    assert all(sum(M[i][k]*M[j][k] for k in range(n)) == (n-1 if i == j else 0) for i in range(n) for j in range(n))
    R = [[x % p for x in r] for r in M]
    best = {}
    for t in (1, 2, 3):
        m = n
        for rows in itertools.combinations(range(n), t):
            for co in itertools.product(range(1, p), repeat=t-1):
                cs = (1,) + co
                w = sum(1 for k in range(n) if sum(c*R[r][k] for c, r in zip(cs, rows)) % p)
                if w < m: m = w
        best[t] = m
    return best
print(json.dumps({"W20": check(W), "Paley20": check(paley())}))
