"""s3: exhaustive k = 5 (N = 32): all 2^15 io prefixes, split into parts.  usage: s3_k5.py PART NPARTS"""
import sys, time
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

part, nparts = int(sys.argv[1]), int(sys.argv[2])
N = 32
t0 = time.time()
free = list(range(2, N - 1, 2))  # a_2, a_4, ..., a_30 : 15 free bits
hist = {}
diam4 = []
diam5 = []
cnt = 0
for bits in range(part, 1 << len(free), nparts):
    a = [0] * (N - 1)
    a[0] = a[1] = 1
    for t, p in enumerate(free):
        b = (bits >> t) & 1
        a[p] = b
        if p + 1 < N - 1:
            a[p + 1] = b
    G = riordan_graph(a, N)
    d = diameter(G)
    hist[d] = hist.get(d, 0) + 1
    cnt += 1
    if d == 5:
        diam5.append(''.join(map(str, a)))
    elif d == 4:
        diam4.append(''.join(map(str, a)))
print('part', part, 'of', nparts, 'count', cnt, 'hist', dict(sorted(hist.items())), 'secs', round(time.time() - t0, 1))
print('diam5', diam5)
# summary of diam-4 prefixes: position of first zero
fz = {}
for s in diam4:
    p = s.index('0')
    fz[p] = fz.get(p, 0) + 1
print('diam4 first-zero positions', dict(sorted(fz.items())))
