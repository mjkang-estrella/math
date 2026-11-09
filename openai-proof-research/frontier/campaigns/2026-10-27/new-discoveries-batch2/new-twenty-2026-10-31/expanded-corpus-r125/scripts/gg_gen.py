# Generate all gamma_g-perfect graphs on n vertices (up to iso) from those on n-1.
# Completeness: perfect G on n vertices: if connected, v of max degree in G-hat gives G = O(G-v, v, Q) with Q a PSC
# of G-v (Thm construction-perf (ii)); if disconnected, remove a vertex of a complete component (Thm (i)).
# In both cases G-v is perfect (hereditary) and N(v) is: complement of a union R of homogeneous cliques of G-v,
# or exactly a complete component of G-v (or empty). We over-generate (any R whose components are homogeneous
# cliques) and keep exactly those passing the recognizer.
import sys, json
sys.path.insert(0, sys.argv[1])
from gg_lib import *
n = int(sys.argv[2]); out = sys.argv[3]
prev = [tuple(json.loads(l)) for l in open(sys.argv[4])] if n > 1 else []
if len(sys.argv) > 6: prev = prev[int(sys.argv[5])::int(sys.argv[6])]
res = set()
if n == 1: res.add(canon([0], 1))
for code in prev:
    m, adj = from_code(code)
    full = (1 << m) - 1
    cl = [adj[x] | (1 << x) for x in range(m)]
    cands = set()
    for c in components(adj, full):
        if is_clique(adj, c): cands.add(c)
    cands.add(0)
    for R in range(1 << m):
        ok = True
        for q in components(adj, R):
            x = (q & -q).bit_length() - 1
            for y in bits(q):
                if cl[y] != cl[x]: ok = False; break
            if not ok or cl[x] & q != q: ok = False
            if not ok: break
        if ok: cands.add(full & ~R)
    for S in cands:
        nadj = adj[:] + [S]
        for y in bits(S): nadj[y] |= 1 << m
        if recog_perfect(nadj, (1 << (m+1)) - 1):
            res.add(canon(nadj, m+1))
with open(out, 'w') as f:
    for c in sorted(res): f.write(json.dumps(list(c)) + '\n')
conn = 0
for c in res:
    k, a = from_code(c)
    if len(components(a, (1 << k) - 1)) == 1: conn += 1
print('n', n, 'perfect', len(res), 'connected', conn)
