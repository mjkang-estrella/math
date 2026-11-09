# Diagnostic for MathDB 327019: a_n = sum_{j=0}^n n!/j! * n^j.  For p = 37 report the n <= N with
# p | a_n and p not dividing n, and the maximum v_p(a_n) seen (computed mod p^3).
import sys
p = int(sys.argv[1]); N = int(sys.argv[2]); M = p ** 3
hits = []; vmax = 0
for n in range(1, N + 1):
    if n % p == 0: continue
    # a_n = sum_j n^j * prod_{i=j+1}^{n} i, accumulate from j = n downwards
    s = 0; prod = 1; pw = pow(n, n, M); inv_n = None
    # iterate j from n down to 0: term_j = n^j * prod_{i=j+1..n} i
    terms = 0; prod = 1
    nj = [1] * (n + 1)
    for j in range(1, n + 1): nj[j] = nj[j - 1] * n % M
    for j in range(n, -1, -1):
        terms = (terms + nj[j] * prod) % M
        prod = prod * j % M if j > 0 else prod
    v = 0; t = terms
    while v < 3 and t % p == 0:
        t //= p; v += 1
    if v >= 1: hits.append((n, v))
    vmax = max(vmax, v)
print(dict(p=p, N=N, schenker_witnesses=hits[:12], count=len(hits), max_valuation_mod_p3=vmax))
