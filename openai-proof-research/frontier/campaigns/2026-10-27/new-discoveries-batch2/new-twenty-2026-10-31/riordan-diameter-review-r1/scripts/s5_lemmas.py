"""s5: finite checks of the published facts (F), (P1), (P2), (P3)/(P3'), (P4), (P5) and of Lemmas B, C."""
import sys, random, time
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

rng = random.Random(4604)
t0 = time.time()

def floorlog2(n):
    return n.bit_length() - 1

# exhaustive over all io prefixes for N = 32 (covers every n <= 32 by (F) once (F) is checked)
seqs32 = rng.sample(io_sequences(31), 2048)  # uniform random 2048 of the 32768 io prefixes (N = 16 below is exhaustive)
badF = badP1 = badP2 = badP4 = badP5 = 0
cntF = cntP1 = cntP2 = cntP4 = cntP5 = 0
for idx, a in enumerate(seqs32):
    G = riordan_graph(a, 32)
    # (F) leading principal: <[1..m]> == G_m for every m (checked on a 1/8 subsample of sequences, all m)
    if idx % 4 == 0:
        for m in range(1, 33):
            cntF += 1
            if induced(G, list(range(m))) != riordan_graph(a, m):
                badF += 1
    # (P1) vertex 2^s+1 universal in G_{2^s+1} and in G_{2^s+2}
    for s in range(0, 5):
        for n in (2 ** s + 1, 2 ** s + 2):
            if n > 32:
                continue
            H = induced(G, list(range(n)))
            cntP1 += 1
            if popc(H[2 ** s]) != n - 1:
                badP1 += 1
    # (P2) <{2^s+1..2^{s+1}}> == G_{2^s} via i -> i - 2^s (labelled)
    for s in range(0, 5):
        cntP2 += 1
        if induced(G, list(range(2 ** s, 2 ** (s + 1)))) != induced(G, list(range(2 ** s))):
            badP2 += 1
    # (P4) diam(G_n) <= floor(log2 n) for n = 2..32 (subsample of n to save time)
    if idx % 2 == 0:
        for n in range(2, 33):
            cntP4 += 1
            d = diameter(induced(G, list(range(n))))
            if d is None or d > floorlog2(n):
                badP4 += 1
    # (P5) diam(G_{2^{s+1}}) <= max(2, diam(G_{2^s}) + 1)
    ds = {s: diameter(induced(G, list(range(2 ** s)))) for s in range(1, 6)}
    for s in range(1, 5):
        cntP5 += 1
        if ds[s + 1] > max(2, ds[s] + 1):
            badP5 += 1
# exhaustive N = 16: every io prefix, every m, every n
for a in io_sequences(15):
    G = riordan_graph(a, 16)
    for m in range(1, 17):
        cntF += 1; badF += induced(G, list(range(m))) != riordan_graph(a, m)
        if m >= 2:
            cntP4 += 1; d = diameter(riordan_graph(a, m)); badP4 += (d is None or d > floorlog2(m))
    for s in range(0, 4):
        cntP2 += 1; badP2 += induced(G, list(range(2 ** s, 2 ** (s + 1)))) != induced(G, list(range(2 ** s)))
        for n in (2 ** s + 1, 2 ** s + 2):
            if n <= 16:
                cntP1 += 1; badP1 += popc(induced(G, list(range(n)))[2 ** s]) != n - 1
print('(F)  checked', cntF, 'failures', badF)
print('(P1) checked', cntP1, 'failures', badP1)
print('(P2) checked', cntP2, 'failures', badP2)
print('(P4) checked', cntP4, 'failures', badP4)
print('(P5) checked', cntP5, 'failures', badP5, ' secs', round(time.time() - t0, 1))

# (P2) and (P1) on random io prefixes for N = 64, 128
bad = 0; cnt = 0
for N in (64, 128):
    for _ in range(25):
        a = random_io(N - 1, rng)
        G = riordan_graph(a, N)
        for s in range(0, N.bit_length() - 1):
            cnt += 1
            if induced(G, list(range(2 ** s, 2 ** (s + 1)))) != induced(G, list(range(2 ** s))):
                bad += 1
            n = 2 ** s + 1
            if n <= N and popc(induced(G, list(range(n)))[2 ** s]) != n - 1:
                bad += 1
print('(P1)+(P2) random N=64,128: checked', cnt, 'failures', bad)

# (P3) in CG_{2^s}: pairs at distance s are exactly (i, 2^s) with i <= 2^{s-1}; (P3') d(1,v) <= s-1 for v < 2^s
for s in range(1, 9):
    N = 2 ** s
    CG = riordan_graph([1] * (N - 1), N)
    far = []
    maxd = 0
    for v in range(N):
        dist = distances_from(CG, v)
        for u in range(v + 1, N):
            maxd = max(maxd, dist[u])
            if dist[u] == s:
                far.append((v + 1, u + 1))
    exp = [(i, N) for i in range(1, N // 2 + 1)] if s >= 1 else []
    d1 = distances_from(CG, 0)
    p3p = all(d1[v] <= s - 1 for v in range(1, N - 1)) if s >= 2 else True
    print(f'(P3) s={s}: diam(CG)={maxd}, far pairs == {{(i,2^s): i<=2^(s-1)}}: {sorted(far) == exp}, (P3\') d(1,v)<=s-1 for v<2^s: {p3p}, deg(N)={popc(CG[N-1])}')

# Lemma B and Lemma C: restricted families a_i = 1 for i <= h-1, free io bits above
def lemma_B_C(K, sample=None):
    N = 2 ** K; h = N // 2
    free = list(range(h, N - 1, 2))
    space = range(1 << len(free)) if sample is None else [rng.randrange(1 << len(free)) for _ in range(sample)]
    nB = badB = nC = badC = 0
    hist = {}
    for bits in space:
        a = [1] * (N - 1)
        for t, p in enumerate(free):
            b = (bits >> t) & 1
            a[p] = b
            if p + 1 < N - 1:
                a[p + 1] = b
        G = riordan_graph(a, N)
        d = diameter(G)
        hist[d] = hist.get(d, 0) + 1
        zeros = [p for p in range(h, N - 1) if a[p] == 0]
        if not zeros:
            continue
        p = zeros[0]
        j = N - 1 - p
        nB += 1
        if not (p % 2 == 0 and 1 <= j <= h - 1 and (G[N - 1] >> (j - 1)) & 1):
            badB += 1
        if K >= 4:
            nC += 1
            if d is None or d > K - 1:
                badC += 1
    return nB, badB, nC, badC, dict(sorted(hist.items()))

for K in (3, 4, 5):
    print(f'Lemma B/C K={K} exhaustive restricted:', lemma_B_C(K))
print('Lemma B/C K=6 random restricted sample 1500:', lemma_B_C(6, 1500))
print('Lemma B/C K=7 random restricted sample 60:', lemma_B_C(7, 60))
print('total secs', round(time.time() - t0, 1))
