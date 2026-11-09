"""s7: checks supporting the reviewer's proposed Lagrange-free Lean route.
  (1) CG Bell entries mod 2 == binom(2i+1-j, i-j) mod 2 == [(i+1) & (i-j) == 0]   (Pascal rule + Kummer)
  (2) dependence: b_{i,j} depends only on a_0..a_{i-j}
  (3) perturbation: if A, A' agree below p then b_{p+j,j}(A) - b_{p+j,j}(A') == (j+1)(a_p - a'_p) mod 2
  (4) CG_{2^K}: last vertex pendant; edge-length bound r(y) <= 2 r(x) with r(x) = N+1-x; universal 2^s+1
  (5) R2 restructured: first zero p at level K (2^(K-1) <= p <= 2^K-2): K >= 4 => diam(G_{2^K}) <= K-1;
      K <= 3 finite cases: p in {2,4} => diam(G_8) = 2; p = 6 => diam(G_16) <= 3 (all 16 io extensions)."""
import sys, random
from math import comb
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1/scripts')
from rcore import *

rng = random.Random(1901)

# (1)
R = 130
rows = bell_rows([1] * (R + 2), R)
bad1 = bad1b = 0
for i in range(R):
    for j in range(i + 1):
        b = (rows[i] >> j) & 1
        if b != comb(2 * i + 1 - j, i - j) % 2:
            bad1 += 1
        if b != (1 if ((i + 1) & (i - j)) == 0 else 0):
            bad1b += 1
print('(1) CG Bell mod 2 vs binom(2i+1-j,i-j) failures', bad1, '; vs bit rule failures', bad1b, '(rows 0..%d)' % (R - 1))

# (2), (3)
bad2 = bad3 = cnt = 0
for _ in range(300):
    n = rng.randrange(8, 70)
    p = rng.randrange(1, n - 1)
    a = [1] + [rng.randrange(2) for _ in range(n)]
    a2 = a[:p] + [rng.randrange(2) for _ in range(n + 1 - p)]
    r1 = bell_rows(a, n); r2 = bell_rows(a2, n)
    for i in range(n):
        for j in range(i + 1):
            g = i - j
            x = (r1[i] >> j) & 1; y = (r2[i] >> j) & 1
            cnt += 1
            if g < p and x != y:
                bad2 += 1
            if g == p and (x ^ y) != ((j + 1) * (a[p] ^ a2[p])) % 2:
                bad3 += 1
print('(2) dependence failures', bad2, '; (3) perturbation failures', bad3, 'over', cnt, 'entries')

# (4)
for K in range(1, 9):
    N = 2 ** K
    CG = riordan_graph([1] * (N - 1), N)
    pend = CG[N - 1] == (1 << (N - 2))
    elen = all(not ((CG[x - 1] >> (y - 1)) & 1) or (N + 1 - y) <= 2 * (N + 1 - x)
               for x in range(1, N + 1) for y in range(1, x))
    univ = all(popc(induced(CG, list(range(2 ** s + 1)))[2 ** s]) == 2 ** s for s in range(K))
    print(f'(4) K={K}: last vertex pendant {pend}; edge-length bound {elen}; vertex 2^s+1 universal in CG_(2^s+1) {univ}')

# (5)
def level(p):
    K = 1
    while not (2 ** (K - 1) <= p <= 2 ** K - 2):
        K += 1
    return K

bad5 = cnt5 = 0
for p in range(2, 127, 2):
    K = level(p)
    if K < 4:
        continue
    N = 2 ** K
    for _ in range(6 if K <= 6 else 2):
        a = random_io(N - 1, rng)
        for t in range(p):
            a[t] = 1
        a[p] = 0
        if p + 1 < N - 1:
            a[p + 1] = 0
        d = diameter(riordan_graph(a, N))
        cnt5 += 1
        if d is None or d > K - 1:
            bad5 += 1
print('(5) K>=4 levels: checked', cnt5, 'random graphs (p = 8..126), failures', bad5)
fin8 = sorted({(''.join(map(str, a)), diameter(riordan_graph(a, 8))) for a in io_sequences(7) if 0 in a[:5]})
print('(5) p in {2,4}: G_8 diameters', fin8)
fin16 = [diameter(riordan_graph(a, 16)) for a in io_sequences(15) if a[:8] == [1, 1, 1, 1, 1, 1, 0, 0]]
print('(5) p = 6: number of io G_16 =', len(fin16), 'diameter histogram', {d: fin16.count(d) for d in set(fin16)})
