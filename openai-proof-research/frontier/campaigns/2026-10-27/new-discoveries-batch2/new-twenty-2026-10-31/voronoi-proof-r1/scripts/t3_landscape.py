# Landscape of the deviator score over deviation shapes c (0<=c_f<=m_f): monotonicity and local maxima.
import sys; sys.path.insert(0, 'scripts')
from vk import *
import itertools
m = tuple(int(a) for a in sys.argv[1:8]); n = sum(m); P = positions(m); cs = coords(m)
S = scores_all(n, P[1:])
def rep(c):
    v = 0; off = 0
    for f in range(7):
        for j in range(c[f]): v |= 1 << (off + j)
        off += m[f]
    return v
shapes = list(itertools.product(*[range(mf + 1) for mf in m]))
sc = {c: int(S[rep(c)]) for c in shapes}
nonmono = 0; locmax = []
for c in shapes:
    nb = []
    for f in range(7):
        for d in (-1, 1):
            c2 = list(c); c2[f] += d
            if 0 <= c2[f] <= m[f]: nb.append(tuple(c2))
    if all(sc[c] >= sc[c2] for c2 in nb) and c != (0,)*7: locmax.append(c)
    for f in range(7):
        if c[f] < m[f]:
            c2 = list(c); c2[f] += 1
            if sc[tuple(c2)] > sc[c]: nonmono += 1
# existence of a weakly decreasing step towards 0
nostep = [c for c in shapes if c != (0,)*7 and not any(c[f] > 0 and sc[tuple(c[i] - (i == f) for i in range(7))] >= sc[c] for f in range(7))]
print('m', m, 'shapes', len(shapes), 'increasing unit steps (c -> c+e_f with higher score):', nonmono)
print('local maxima other than 0 (score*8):', [(c, round(float(frac(sc[c], n) * 8), 4)) for c in locmax][:20], 'count', len(locmax))
print('shapes with no weakly-increasing step towards 0:', len(nostep), nostep[:10])
# score as function of |c|
by = {}
for c in shapes:
    k = sum(c); by.setdefault(k, []).append(sc[c])
print('max score*8 by |c|:', [(k, round(float(frac(max(v), n) * 8), 4)) for k, v in sorted(by.items())])
