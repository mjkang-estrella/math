# For restricted A-sequences (first 2^(K-1) entries ones, some later zero), test whether vertex N=2^K
# has a neighbour in [1, 2^(K-1)] in G_N; report the first-zero positions where it fails.
import sys, json, random, collections
sys.path.insert(0, 'scripts')
from riordan_fast import rows_from_a, adjacency, make_a
K = int(sys.argv[1]); n = 2 ** K; h = n // 2; L = n - 1
free = list(range(h, L, 2))
mode = sys.argv[2]
it = range(2 ** len(free)) if mode == 'all' else [random.Random(7).getrandbits(len(free)) for _ in range(int(mode))]
fails = collections.Counter(); tested = 0; firstzero_stats = collections.Counter()
for idx in it:
    bits = [(idx >> (len(free) - 1 - q)) & 1 for q in range(len(free))]
    if all(bits): continue
    a = make_a(n, h, bits, free)
    R = rows_from_a(a, n - 1)
    row = R[n - 2] << 1            # neighbours j<N of N: bit j
    low = row & ((1 << (h + 1)) - 2)
    p = a.index(0)
    tested += 1
    if not low: fails[p] += 1
    firstzero_stats[p] += 1
print(json.dumps({'K': K, 'tested': tested, 'fail_by_first_zero': dict(sorted(fails.items())), 'tested_by_first_zero': dict(sorted(firstzero_stats.items()))}))
