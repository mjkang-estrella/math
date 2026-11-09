"""Exhaustive 2-variable check of the Amit-Ashurst conjecture (MathDB 353267) for a concrete nilpotent group G:
enumerate ALL word maps G^2 -> G (the relatively free group F_2(G), closure of the projections under pointwise
multiplication), and for each word map and each g in its image check #{(a,b): w(a,b)=g} >= |G|.
Groups: UT4F2 (4x4 unitriangular over F_2, order 64, class 3), UT3F3 (order 27), D16 (dihedral, order 16) control.
Usage: amit_ashurst_k2.py GROUP CAP"""
import sys, itertools
name, CAP = sys.argv[1], int(sys.argv[2])
def matgroup(nn, p):
    pos = [(i, j) for i in range(nn) for j in range(i + 1, nn)]
    els = []
    for vals in itertools.product(range(p), repeat=len(pos)):
        M = [[1 if i == j else 0 for j in range(nn)] for i in range(nn)]
        for (i, j), v in zip(pos, vals): M[i][j] = v
        els.append(tuple(map(tuple, M)))
    idx = {e: k for k, e in enumerate(els)}
    def mul(A, B):
        return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(nn)) % p for j in range(nn)) for i in range(nn))
    T = [[idx[mul(a, b)] for b in els] for a in els]
    return T
def dihedral(n):
    els = [(r, s) for s in range(2) for r in range(n)]
    idx = {e: k for k, e in enumerate(els)}
    def mul(a, b):
        r1, s1 = a; r2, s2 = b
        return ((r1 + (-r2 if s1 else r2)) % n, (s1 + s2) % 2)
    return [[idx[mul(a, b)] for b in els] for a in els]
T = {'UT4F2': lambda: matgroup(4, 2), 'UT3F3': lambda: matgroup(3, 3), 'D16': lambda: dihedral(8)}[name]()
N = len(T)
e = next(i for i in range(N) if all(T[i][j] == j for j in range(N)))
inv = [next(j for j in range(N) if T[i][j] == e) for i in range(N)]
X = bytes(a for a in range(N) for b in range(N)) if N <= 256 else None
Y = bytes(b for a in range(N) for b in range(N))
gens = [X, Y, bytes(inv[v] for v in X), bytes(inv[v] for v in Y)]
def mulmap(f, g): return bytes(T[a][b] for a, b in zip(f, g))
ident = bytes([e]) * (N * N)
seen = {ident}; frontier = [ident]
while frontier:
    nf = []
    for f in frontier:
        for g in gens:
            h = mulmap(f, g)
            if h not in seen:
                seen.add(h); nf.append(h)
                if len(seen) > CAP:
                    print('CAP exceeded', len(seen)); sys.exit(2)
    frontier = nf
worst = None; viol = []
for f in seen:
    cnt = [0] * N
    for v in f: cnt[v] += 1
    m = min(c for c in cnt if c)
    if worst is None or m < worst: worst = m
    if m < N: viol.append((m, f[:16]))
print('group', name, 'order', N, 'distinct 2-variable word maps |F_2(G)|', len(seen),
      'min positive fiber size', worst, 'threshold |G|', N, 'violations', len(viol), viol[:3])
