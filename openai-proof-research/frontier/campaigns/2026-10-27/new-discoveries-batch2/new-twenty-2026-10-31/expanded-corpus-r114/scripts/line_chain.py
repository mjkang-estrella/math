# s(L(G)) for chains C_a -(bridge path of p edges)- C_b -(bridge path of q edges)- C_c, where the middle cycle is
# entered at vertex 0 and left at vertex j; p or q = 0 means the cycles share a vertex.
import numpy as np, itertools
def sig_line(E):
    m = len(E); L = np.zeros((m, m))
    for i, j in itertools.combinations(range(m), 2):
        if set(E[i]) & set(E[j]): L[i, j] = L[j, i] = 1
    ev = np.linalg.eigvalsh(L); return int((ev > 1e-8).sum() - (ev < -1e-8).sum())
def build(a, b, c, j, p, q):
    E = []; nv = [0]
    def new(): nv[0] += 1; return nv[0] - 1
    A = [new() for _ in range(a)]; E += [(A[i], A[(i + 1) % a]) for i in range(a)]
    def path(u, length):
        for _ in range(length): w = new(); E.append((u, w)); u = w
        return u
    s = path(A[0], p)
    B = [s] + [new() for _ in range(b - 1)]; E += [(B[i], B[(i + 1) % b]) for i in range(b)]
    t = path(B[j], q)
    C = [t] + [new() for _ in range(c - 1)]; E += [(C[i], C[(i + 1) % c]) for i in range(c)]
    return E, nv[0]
rows = []
for a, c in [(5, 5), (5, 9), (9, 9), (5, 13)]:
    for b in range(3, 9):
        for j in range(0, b // 2 + 1):
            for p in range(0, 3):
                for q in range(0, 3):
                    E, n = build(a, b, c, j, p, q); s = sig_line(E)
                    if s >= 2: rows.append((n, len(E), a, b, c, j, p, q, s))
rows.sort()
print('count with s>=2:', len(rows))
for r in rows[:25]: print('n=%d m=%d a=%d b=%d c=%d j=%d p=%d q=%d s=%d' % r)
