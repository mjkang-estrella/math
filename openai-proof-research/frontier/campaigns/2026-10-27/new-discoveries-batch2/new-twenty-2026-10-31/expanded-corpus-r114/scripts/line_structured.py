# Signature s(L(G)) = n+ - n- of line graphs of structured connected graphs built from odd cycles C_{4k+1}
# (the source's tight examples), to see whether simple gluings already exceed the bound s <= 1.
import numpy as np, itertools, json
def sig_line(E):
    m = len(E); L = np.zeros((m, m))
    for i, j in itertools.combinations(range(m), 2):
        if set(E[i]) & set(E[j]): L[i, j] = L[j, i] = 1
    ev = np.linalg.eigvalsh(L); return int((ev > 1e-8).sum() - (ev < -1e-8).sum())
def cycle(k, off): return [(off + i, off + (i + 1) % k) for i in range(k)]
out = []
# dumbbell: C_a and C_b joined by a path with l edges (l=0: share a vertex)
for a, b in [(5, 5), (5, 9), (9, 9)]:
    for l in range(0, 6):
        E = cycle(a, 0) + cycle(b, a + max(l - 1, 0)) if False else None
        E = cycle(a, 0); nxt = a; prev = 0
        for t in range(l - 1): E.append((prev, nxt)); prev = nxt; nxt += 1
        C = [(nxt + i, nxt + (i + 1) % b) for i in range(b)]
        if l == 0: C = [((0 if u == nxt else u), (0 if v == nxt else v)) for u, v in C]
        else: E.append((prev, nxt))
        E += C; out.append((f'dumbbell C{a}-P{l}-C{b}', sig_line(E)))
# chain of t pentagons joined by single edges
for t in range(2, 6):
    E = []
    for s in range(t):
        E += cycle(5, 5 * s)
        if s: E.append((5 * s - 3, 5 * s))
    out.append((f'chain of {t} C5 by bridges', sig_line(E)))
# pentagons sharing a common vertex (friendship-like)
for t in range(2, 5):
    E = []
    for s in range(t):
        vs = [0] + [1 + 4 * s + i for i in range(4)]
        E += [(vs[i], vs[(i + 1) % 5]) for i in range(5)]
    out.append((f'{t} C5 sharing a vertex', sig_line(E)))
for name, s in out: print(name, 's(L)=', s)
