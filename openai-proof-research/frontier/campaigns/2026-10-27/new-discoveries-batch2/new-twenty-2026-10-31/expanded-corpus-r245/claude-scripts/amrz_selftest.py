"""Cross-check amrz.lam_mu against a naive Floyd-Warshall implementation (read-only)."""
import importlib.util
import sys
import time

spec = importlib.util.spec_from_file_location('amrz', sys.argv[1])
A = importlib.util.module_from_spec(spec)
spec.loader.exec_module(A)


def naive(n, adj):
    INF = 99
    d = [[0 if i == j else (1 if adj[i] >> j & 1 else INF) for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if d[i][k] + d[k][j] < d[i][j]:
                    d[i][j] = d[i][k] + d[k][j]
    lines = set()
    mu = 0
    for u in range(n):
        for v in range(u + 1, n):
            L = frozenset(w for w in range(n) if d[u][v] == d[u][w] + d[w][v]
                          or d[u][v] == abs(d[u][w] - d[w][v]))
            lines.add(L)
            if len(L) == n:
                mu += 1
    return len(lines), mu


t = time.time()
tot = 0
for N in range(2, 9):
    gs = A.read_list(N)
    step = 1 if N < 8 else 7
    for g in gs[::step]:
        a = A.lam_mu(N, list(g))
        b = naive(N, list(g))
        tot += 1
        if a != b:
            print('MISMATCH', N, g, a, b)
            sys.exit(1)
# named examples
C4 = [0b1010, 0b0101, 0b1010, 0b0101]
print('C4', A.lam_mu(4, C4), naive(4, C4))
P4 = [0b0010, 0b0101, 0b1010, 0b0100]
print('P4', A.lam_mu(4, P4))
print('ok', tot, 'graphs', round(time.time() - t, 1), 's')
