# Exhaustive (numerical) search for extreme n-subsets of Z_p up to affine equivalence.
# Necessary condition: every nonzero difference of E occurs >= 2 times in E-E (a single unimodular product cannot vanish).
import sys; sys.path.append("/home/mj-kang/.local/lib/python3.14/site-packages")
import itertools, json
import numpy as np
sys.path.insert(0, sys.argv[1])
from extreme_num import best
p = int(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(',')]; rs = int(sys.argv[4])
rng = np.random.default_rng(12345)
maps = [(a, b) for a in range(1, p) for b in range(p)]
def canon(S):
    return min(tuple(sorted((a*x+b) % p for x in S)) for a, b in maps)
out = {}
for n in ns:
    classes = set(); passed = 0
    for rest in itertools.combinations(range(2, p), n-2):
        S = (0, 1) + rest
        cnt = [0]*p
        for x in S:
            for y in S:
                if x != y: cnt[(x-y) % p] += 1
        if any(c == 1 for c in cnt): continue
        passed += 1
        classes.add(canon(S))
    ext = []
    for C in sorted(classes):
        v, t = best(list(C), p, rs, rng)
        if v < 1e-14: ext.append(C)
    out[n] = {'classes_after_prune': len(classes), 'extreme_numerical': [list(c) for c in ext]}
    print('p', p, 'n', n, 'pruned classes', len(classes), 'numerically extreme', len(ext), [list(c) for c in ext], flush=True)
