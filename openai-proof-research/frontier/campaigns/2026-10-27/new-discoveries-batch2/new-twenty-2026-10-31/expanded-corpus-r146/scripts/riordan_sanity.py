# Sanity checks (diagnostics, not proofs) for the 337352 argument.
import sys, json, random
sys.path.insert(0, 'scripts')
from riordan_fast import rows_from_a, adjacency, ecc_all, make_a
def dists_from(adj, n, s):
    d = {s: 0}; front = [s]
    while front:
        nxt = []
        for v in front:
            m = adj[v]
            while m:
                low = m & -m; u = low.bit_length() - 1; m ^= low
                if u not in d: d[u] = d[v] + 1; nxt.append(u)
        front = nxt
    return d
res = {}
# (1) Jung Thm 2.6 consequence: in CG_{2^s}, d(1,v) <= s-1 for v<2^s and d(1,2^s)=s; also h+1 universal in G_{h+1} for io sequences sampled
for s in range(2, 9):
    n = 2 ** s; adj = adjacency(rows_from_a([1] * n, n - 1), n); d = dists_from(adj, n, 1)
    res[f'CG_{n}'] = dict(d1_to_n=d[n], max_d1_other=max(d[v] for v in range(2, n)), diam=ecc_all(adj, n, 10**9))
# (2) random restricted sample at K=7 (first 64 entries ones, random tail): diameter <= 6 unless all ones
rnd = random.Random(11); K = 7; n = 128; h = 64; free = list(range(h, n - 1, 2)); worst = 0; cnt = 0
for t in range(3000):
    bits = [rnd.randint(0, 1) for _ in free]
    if all(bits): continue
    a = make_a(n, h, bits, free); adj = adjacency(rows_from_a(a, n - 1), n)
    d = ecc_all(adj, n, 10**9); worst = max(worst, d); cnt += 1
    p = a.index(0); j = n - 1 - p
    assert adj[n] >> j & 1 and 1 <= j <= h - 1
res['K7_random_restricted'] = dict(samples=cnt, max_diam=worst, low_neighbour_j_eq_N_minus_1_minus_p_always=True)
print(json.dumps(res, indent=1))
