# Exact all-v convolution check for one subspace profile; prints max deviation score and the
# top few deviation shapes.  Usage: t2_family.py m1 ... m7
import sys; sys.path.insert(0, 'scripts')
from vk import *
import time
m = tuple(int(a) for a in sys.argv[1:8]); n = sum(m); P = positions(m)
t0 = time.time()
others = P[1:]
S = scores_all(n, others)
cs = coords(m)
# shape of v: c_f = number of ones of v in class f
x = np.arange(1 << n, dtype=np.int64)
shape = np.zeros((1 << n, 7), dtype=np.int64)
for j, f in enumerate(cs):
    shape[:, f - 1] += (x >> j) & 1
key = np.zeros(1 << n, dtype=np.int64)
for f in range(7):
    key = key * 32 + shape[:, f]
# consistency: S constant on each shape
order = np.argsort(key, kind='stable'); ks = key[order]; ss = S[order]
br = np.flatnonzero(np.diff(ks)) + 1
starts = np.concatenate([[0], br]); ends = np.concatenate([br, [len(ks)]])
const = all(ss[a] == ss[b - 1] and ss[a:b].min() == ss[a:b].max() for a, b in zip(starts, ends))
vals = [(int(ss[a]), tuple(int(z) for z in shape[order[a]])) for a in starts]
vals.sort(reverse=True)
eighth = (L << n) // 8
print('m', m, 'n', n, 'score at v=0', frac(S[0], n), 'equals 1/8:', S[0] * 8 == (L << n))
print('score constant on shapes:', const, 'number of shapes', len(vals))
print('max over v != 0:', frac(np.max(S[1:]), n), ' -> EQUILIBRIUM' if np.max(S) * 8 <= (L << n) else ' -> NOT equilibrium')
print('vertices v with score >= 1/8:', int((S * 8 >= (L << n)).sum()))
for s, c in vals[:12]:
    print('  shape c =', c, 'score', frac(s, n), float(frac(s, n)) * 8)
print('time', round(time.time() - t0, 1))
