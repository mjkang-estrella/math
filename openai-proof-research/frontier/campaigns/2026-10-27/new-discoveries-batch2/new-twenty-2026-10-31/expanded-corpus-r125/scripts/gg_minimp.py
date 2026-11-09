# Find all minimally gamma_g-imperfect graphs on N vertices.
# G minimal imperfect => G has no true twins (twin contraction is a proper induced subgraph; fact (iv) of source).
# Pick u of maximum degree in G. H = G-u is perfect, true-twin classes of H have size <= 2 and u splits each.
import sys, json
sys.path.insert(0, sys.argv[1])
from gg_lib import *
N = int(sys.argv[2]); out = sys.argv[3]
prev = [tuple(json.loads(l)) for l in open(sys.argv[4])]
if len(sys.argv) > 6: prev = prev[int(sys.argv[5])::int(sys.argv[6])]
found = {}; stats = {'H': 0, 'H_twinok': 0, 'cand': 0, 'gamma2': 0, 'gamma3plus': 0, 'imperfect_top': 0}
g3 = []
for code in prev:
    m, adj = from_code(code); stats['H'] += 1
    cl = [adj[x] | (1 << x) for x in range(m)]
    classes = {}
    for x in range(m): classes.setdefault(cl[x], []).append(x)
    if any(len(c) > 2 for c in classes.values()): continue
    stats['H_twinok'] += 1
    forced = 0; singles = []
    for c in classes.values():
        if len(c) == 2: forced |= 1 << c[0]
        else: singles.append(c[0])
    degH = [popc(adj[x]) for x in range(m)]
    for t in range(1 << len(singles)):
        S = forced
        for k, x in enumerate(singles):
            if t >> k & 1: S |= 1 << x
        s = popc(S)
        if s >= m: continue  # u universal => gamma 1
        if any(degH[x] + (S >> x & 1) > s for x in range(m)): continue
        stats['cand'] += 1
        nadj = adj[:] + [S]
        for y in bits(S): nadj[y] |= 1 << m
        r = imperfect_top(nadj, N)
        full = (1 << N) - 1
        if r is False: continue
        if not all(recog_perfect(nadj, full & ~(1 << w)) for w in range(N)): continue
        if r is None:
            stats['gamma3plus'] += 1
            if gamma_g(nadj, full) == gamma(nadj, full): continue
            g3.append(nadj)
        stats['imperfect_top'] += 1
        if True:
            c = canon(nadj, N)
            found[c] = found.get(c, 0) + 1
with open(out, 'w') as f:
    for c in sorted(found): f.write(json.dumps(list(c)) + '\n')
print('N', N, 'minimal imperfect found', len(found), stats, 'gamma>=3 imperfect tops', len(g3))
