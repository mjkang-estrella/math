# Mattheus Conjecture 6.2.7 / Kiss-Marko-Nagy-Somlai Conj. 7.2: A subset F_p^3, |A|=p,
# A not in a plane => A determines >= p+1 (possibly p+2) directions.
# WLOG (AGL(3,p)) A contains 0,e1,e2,e3 (any non-coplanar set has 4 affinely independent points).
# Enumerate the remaining p-4 points as combinations from F_p^3 \ {0,e1,e2,e3}.
# usage: directions.py p [first_index_start first_index_end]  (split on the smallest extra point index)
import sys, itertools
p = int(sys.argv[1])
pts = [(a, b, c) for a in range(p) for b in range(p) for c in range(p)]
base = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]
rest = [q for q in pts if q not in base]
inv = [0] + [pow(i, p - 2, p) for i in range(1, p)]
def norm(v):
    for x in v:
        if x:
            t = inv[x]
            return tuple((y * t) % p for y in v)
    raise ValueError
idx = {q: i for i, q in enumerate(pts)}
# precompute direction id for each ordered pair index difference
dirid = {}
def did(u, v):
    d = tuple((a - b) % p for a, b in zip(u, v))
    return norm(d)
P = len(pts)
D = [[None] * P for _ in range(P)]
for i in range(P):
    for j in range(P):
        if i != j: D[i][j] = did(pts[i], pts[j])
basedirs = set(D[idx[a]][idx[b]] for a, b in itertools.combinations(base, 2))
k = p - 4
lo = int(sys.argv[2]) if len(sys.argv) > 2 else 0
hi = int(sys.argv[3]) if len(sys.argv) > 3 else len(rest)
minN = None; minex = []; cnt = 0
bi = [idx[b] for b in base]
for first in range(lo, hi):
    for tail in itertools.combinations(range(first + 1, len(rest)), k - 1):
        sel = [idx[rest[first]]] + [idx[rest[t]] for t in tail]
        dirs = set(basedirs)
        allp = bi + sel
        for x in sel:
            for y in allp:
                if y != x: dirs.add(D[x][y])
        cnt += 1
        N = len(dirs)
        if minN is None or N < minN:
            minN = N; minex = [[pts[i] for i in allp]]
        elif N == minN and len(minex) < 5:
            minex.append([pts[i] for i in allp])
print('p', p, 'range', lo, hi, 'sets', cnt, 'min #directions', minN, 'bound p+1 =', p + 1)
for e in minex: print('  ', e)
