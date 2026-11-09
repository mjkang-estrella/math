# Explicit small cases for 337352 and a recomputation of Jung (arXiv:1901.11156) Tables 1-2; plus the low-neighbour formula check.
import sys, json
sys.path.insert(0, 'scripts')
import riordan
from riordan_fast import rows_from_a, adjacency, ecc_all, make_a
out = {}
for k in (2, 3):
    n = 2 ** k; cg = riordan.graph([1] * n, n)
    for a in riordan.io_sequences(n):
        adj = riordan.graph(a, n); d = riordan.diameter(adj, n)
        if d == k:
            edges = sorted((j, i) for i in range(1, n + 1) for j in range(1, i) if adj[i] >> j & 1)
            out[f'k{k}_' + ''.join(map(str, a))] = dict(diam=d, isomorphic_to_CG=riordan.isomorphic(adj, cg, n), edges=edges)
# Jung Table 1 (n=8): all 8 io sequences
out['table1_n8'] = {''.join(map(str, a)): riordan.diameter(riordan.graph(a, 8), 8) for a in riordan.io_sequences(8)}
# Jung Table 2 rows (n=16, first six entries ones)
t2 = {}
for a in riordan.io_sequences(16):
    if a[:6] == [1] * 6:
        t2[''.join(map(str, a))] = riordan.diameter(riordan.graph(a, 16), 16)
out['table2_n16_first6ones'] = t2
# low-neighbour formula: for every Bell-type binary A (not only io) with N=2^K, N~j iff j odd and [w^(N-1-j)] 1/A = 1 (mod 2)
def inv_mod2(a, L):
    b = [0] * L; b[0] = 1
    for m in range(1, L):
        s = 0
        for t in range(1, m + 1):
            if t < len(a): s ^= a[t] & b[m - t]
        b[m] = s
    return b
import random
rnd = random.Random(3); checked = 0
for K in (3, 4, 5, 6):
    N = 2 ** K
    for trial in range(200):
        a = [1] + [rnd.randint(0, 1) for _ in range(N)]
        R = rows_from_a(a, N - 1)
        adj = adjacency(R, N)
        ia = inv_mod2(a, N)
        for j in range(1, N):
            pred = (j % 2 == 1) and ia[N - 1 - j] == 1
            assert pred == bool(adj[N] >> j & 1), (K, j)
        checked += 1
out['lagrange_neighbour_formula_checked_random_A'] = checked
print(json.dumps(out, indent=1))
