import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import itertools, time
from subspace import check
d = int(sys.argv[1]); nmin = int(sys.argv[2]); nmax = int(sys.argv[3])
F = list(range(1, 1 << d))
# GL(d,2) as permutations of nonzero functionals
def apply(M, f):  # M: list of d column images; f as vector
    r = 0
    for b in range(d):
        if f >> b & 1: r ^= M[b]
    return r
perms = []
for M in itertools.product(F, repeat=d):
    imgs = [apply(M, f) for f in F]
    if len(set(imgs)) == len(F) and 0 not in imgs:
        perms.append([F.index(x) for x in imgs])
def canon(mult):
    best = None
    for p in perms:
        v = [0] * len(F)
        for a, b in enumerate(p): v[b] = mult[a]
        t = tuple(v)
        if best is None or t > best: best = t
    return best
def comps(n, parts):
    if parts == 1: yield (n,); return
    for a in range(n + 1):
        for r in comps(n - a, parts - 1): yield (a,) + r
t0 = time.time()
for n in range(nmin, nmax + 1):
    seen = set(); eq = []; tot = 0
    for m in comps(n, len(F)):
        c = canon(m)
        if c in seen: continue
        seen.add(c); tot += 1
        nn, cur, best, arg, fair = check(d, list(c))
        if best <= cur: eq.append(c)
    print('d', d, 'n', n, 'orbits', tot, 'equilibria', len(eq), eq[:30], 'time', round(time.time() - t0, 1), flush=True)
