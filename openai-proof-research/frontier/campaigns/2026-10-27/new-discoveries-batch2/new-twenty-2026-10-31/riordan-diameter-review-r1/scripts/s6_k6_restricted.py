"""s6: K = 6 restricted family (a_0..a_31 = 1, io-free a_32..a_62): exhaustive 2^16 diameters, Lemma B and Lemma C. usage: PART NPARTS"""
import sys, time
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *
part, nparts = int(sys.argv[1]), int(sys.argv[2])
K = 6; N = 64; h = 32
free = list(range(h, N - 1, 2))
t0 = time.time()
hist = {}; badB = badC = n = 0; d6 = []; d5 = []
for bits in range(part, 1 << len(free), nparts):
    a = [1] * (N - 1)
    for t, p in enumerate(free):
        b = (bits >> t) & 1
        a[p] = b
        if p + 1 < N - 1:
            a[p + 1] = b
    G = riordan_graph(a, N)
    d = diameter(G)
    hist[d] = hist.get(d, 0) + 1
    n += 1
    s = ''.join(map(str, a))
    if d == 6: d6.append(s)
    if d == 5: d5.append(s)
    zeros = [p for p in range(h, N - 1) if a[p] == 0]
    if zeros:
        p = zeros[0]; j = N - 1 - p
        if not (p % 2 == 0 and 1 <= j <= h - 1 and (G[N - 1] >> (j - 1)) & 1): badB += 1
        if d is None or d > K - 1: badC += 1
print('part', part, '/', nparts, 'count', n, 'hist', dict(sorted(hist.items())), 'LemmaB failures', badB, 'LemmaC failures', badC, 'secs', round(time.time() - t0, 1))
print('diam6', d6)
print('diam5', d5)
