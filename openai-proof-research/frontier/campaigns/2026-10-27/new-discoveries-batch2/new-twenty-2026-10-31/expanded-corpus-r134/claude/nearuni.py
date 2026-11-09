import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Near-uniform multiplicity vectors (entries in {t, t+1, ..., t+spread}) up to GL(3,2), for a given n.
import itertools, time
from subspace import check
from subscan_chunk_lib import canon
n = int(sys.argv[1]); spread = int(sys.argv[2]); lo = int(sys.argv[3]); hi = int(sys.argv[4])
cands = set()
for t in range(0, n + 1):
    for v in itertools.product(range(t, t + spread + 1), repeat=7):
        if sum(v) == n: cands.add(canon(v))
cands = sorted(cands, reverse=True)
print('n', n, 'spread', spread, 'orbits', len(cands), flush=True)
for c in cands[lo:hi]:
    t0 = time.time(); nn, cur, best, arg, fair = check(3, list(c))
    print(c, 'EQ' if best <= cur else 'NOT', 'rel_gain', round((best - cur) / cur, 6), 'arg', bin(arg), round(time.time() - t0, 1), flush=True)
