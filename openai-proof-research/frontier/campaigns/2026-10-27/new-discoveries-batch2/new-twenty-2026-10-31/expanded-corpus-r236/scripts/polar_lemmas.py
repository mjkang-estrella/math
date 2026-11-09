"""Machine checks of the intermediate lemmas of the 350432 proof (CANDIDATE.md), against the exact cotree DP.
 L1  cluster with c components, r' nontrivial: (inf,k)-polar iff min(r', c-1) <= k.
 L3  G = iK1 + (K_{s_1}+...+K_{s_r}) + Q, Q connected non-complete: (inf,k)-polar iff
     Q (1,k-r)-polar or Q (inf,k-r-i)-polar.
 L6  connected cograph Q, (1,l+1)-polar, not (1,l)-polar, l >= 1  =>  Q = coK_a (+) cluster with l+1 cliques.
 L7  Q = coK_a (+) C, C cluster with m >= 2 cliques, beta = #cliques of size >= 2:
     (a) for 1 <= p <= m-1: (1,p)-polar iff (a=1 and beta<=1) or (beta=0 and a<=p);
     (b) for p >= 0: (inf,p)-polar iff min(beta, m-1) <= p.
Usage: polar_lemmas.py N SCRIPTDIR"""
import sys, importlib.util, itertools
N, SD = int(sys.argv[1]), sys.argv[2]
sys.argv = ['polar_cographs.py', str(N), '0', '0', '/dev/null']
spec = importlib.util.spec_from_file_location('pc', SD + '/polar_cographs.py')
pc = importlib.util.module_from_spec(spec); spec.loader.exec_module(pc)
pc.CAP = 10 ** 6; pc.states.cache_clear()
V, mk, PI, P1 = pc.V, pc.mk, pc.polar_inf, pc.polar_one
U = lambda xs: mk('U', xs); J = lambda xs: mk('J', xs)
def K(s): return V if s == 1 else J([V] * s)
def coK(s): return V if s == 1 else U([V] * s)
def cluster(sizes): return U([K(s) for s in sizes])
def is_complete(g): return g == V or (g[0] == 'J' and all(c == V for c in g[1]))
cnt = {'L1': 0, 'L3': 0, 'L6': 0, 'L7a': 0, 'L7b': 0}
# L1
for c in range(1, 8):
    for sizes in itertools.combinations_with_replacement(range(1, 5), c):
        g = cluster(list(sizes)); rp = sum(1 for s in sizes if s >= 2)
        for k in range(0, 9):
            assert PI(g, k) == (min(rp, c - 1) <= k), ('L1', sizes, k); cnt['L1'] += 1
# L3
Qs = [q for n in range(3, 9) for q in pc.conn[n] if not is_complete(q)]
for q in Qs:
    for i in range(0, 3):
        for sizes in [(), (2,), (3,), (2, 2), (2, 3)]:
            g = U([V] * i + [K(s) for s in sizes] + [q]); r = len(sizes)
            for k in range(0, 6):
                rhs = (k - r >= 0 and P1(q, k - r)) or (k - r - i >= 0 and PI(q, k - r - i))
                assert PI(g, k) == rhs, ('L3', pc.show(g), k); cnt['L3'] += 1
# L6
def is_coK_join_cluster(q, m):
    if q == V or q[0] != 'J': return False
    ch = list(q[1])
    # a cluster with m >= 2 cliques, and an edgeless graph with >= 2 vertices, are each co-connected,
    # so q = coK_a (+) C has exactly two co-components; try both orders.
    if len(ch) != 2: return False
    is_cl = lambda b: b != V and b[0] == 'U' and all(is_complete(x) for x in b[1]) and len(b[1]) == m
    is_el = lambda b: b == V or (b[0] == 'U' and all(x == V for x in b[1]))
    return (is_cl(ch[0]) and is_el(ch[1])) or (is_cl(ch[1]) and is_el(ch[0]))
for n in range(2, N + 1):
    for q in pc.conn[n]:
        for l in range(1, 7):
            if P1(q, l + 1) and not P1(q, l):
                assert is_coK_join_cluster(q, l + 1), ('L6', pc.show(q), l); cnt['L6'] += 1
# L7
for a in range(1, 5):
    for m in range(2, 6):
        for sizes in itertools.combinations_with_replacement(range(1, 4), m):
            q = J([coK(a), cluster(list(sizes))]); beta = sum(1 for s in sizes if s >= 2)
            for p in range(1, m):
                assert P1(q, p) == ((a == 1 and beta <= 1) or (beta == 0 and a <= p)), ('L7a', a, sizes, p); cnt['L7a'] += 1
            for p in range(0, m + 2):
                assert PI(q, p) == (min(beta, m - 1) <= p), ('L7b', a, sizes, p); cnt['L7b'] += 1
print('all lemma checks passed', cnt)
