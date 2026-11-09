import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Chunked version of subscan.py: orbits of multiplicity vectors under GL(3,2), deterministic order;
# checks orbit indices [lo, hi) and writes results to logs/subscan-n{n}-{lo}-{hi}.json
import itertools, time, json
from subspace import check
d = 3; n = int(sys.argv[1]); lo = int(sys.argv[2]); hi = int(sys.argv[3])
F = list(range(1, 1 << d))
def apply(M, f):
    r = 0
    for b in range(d):
        if f >> b & 1: r ^= M[b]
    return r
perms = []
for M in itertools.product(F, repeat=d):
    imgs = [apply(M, f) for f in F]
    if len(set(imgs)) == len(F): perms.append([F.index(x) for x in imgs])
assert len(perms) == 168
def canon(m):
    best = None
    for p in perms:
        v = [0] * 7
        for a, b in enumerate(p): v[b] = m[a]
        t = tuple(v)
        if best is None or t > best: best = t
    return best
def comps(n, parts):
    if parts == 1: yield (n,); return
    for a in range(n + 1):
        for r in comps(n - a, parts - 1): yield (a,) + r
orbits = sorted({canon(m) for m in comps(n, 7)}, reverse=True)
t0 = time.time(); res = []
for idx in range(lo, min(hi, len(orbits))):
    c = orbits[idx]
    nn, cur, best, arg, fair = check(d, list(c))
    res.append([list(c), best <= cur, arg])
out = {'n': n, 'total_orbits': len(orbits), 'lo': lo, 'hi': min(hi, len(orbits)), 'equilibria': [r[0] for r in res if r[1]],
       'checked': len(res), 'time': round(time.time() - t0, 1)}
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'logs/subscan-n{n}-{lo}-{hi}.json'), 'w').write(json.dumps(out) + '\n')
print(n, 'orbits', len(orbits), 'range', lo, out['hi'], 'eq', len(out['equilibria']), 'time', out['time'])
