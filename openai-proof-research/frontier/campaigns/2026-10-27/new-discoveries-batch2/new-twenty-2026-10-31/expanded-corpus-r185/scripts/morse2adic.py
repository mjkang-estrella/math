"""Postnikov 2-adic conjecture (MathDB 343468) diagnostic.
L_n = weighted Catalan number with weight b(h) = (2h+1)^2 on an up-step starting at height h
(Gao-Gu arXiv:1908.03914, Sec. 4; Postnikov-Sagan). C_n = Catalan.
Conjecture: exists 2-adic alpha = ...010111_2 with  v2(L_n - C_n) = s2(n) + v2(n - alpha) + 2  for all n >= 2.
Equivalently r_n := v2(L_n-C_n) - s2(n) - 2 must equal v2(n - alpha).
Usage: morse2adic.py N  -> computes n <= N, checks consistency, prints the bits of alpha forced.
"""
import sys
from math import comb
N = int(sys.argv[1]); k = int(sys.argv[2]) if len(sys.argv) > 2 else 1

def v2(x):
    if x == 0: return None
    return (x & -x).bit_length() - 1

def weighted_catalan(N, b):
    # f[h] = weighted count of paths of current length ending at height h
    out = [1]
    f = [1]
    for step in range(1, 2 * N + 1):
        g = [0] * (min(step, 2 * N - step) + 1)
        for h, val in enumerate(f):
            if val == 0: continue
            if h + 1 < len(g): g[h + 1] += val * b(h)
            if h - 1 >= 0 and h - 1 < len(g): g[h - 1] += val
        f = g
        if step % 2 == 0: out.append(f[0])
    return out

L = weighted_catalan(N, lambda h: (2 * h + 1) ** (2 * k))
print("L[:6]", L[:6])
r = {}
for n in range(2, N + 1):
    C = comb(2 * n, n) // (n + 1)
    d = L[n] - C
    vd = v2(d)
    r[n] = None if vd is None else vd - bin(n).count('1') - 2
# Consistency: r_n = v2(n - alpha). For each j, alpha mod 2^(j+1) is pinned by any n with r_n >= j... specifically
# r_n = t means n = alpha mod 2^t and n != alpha mod 2^(t+1).
# Build alpha bit by bit: alpha mod 2^(t+1) = n + 2^t mod 2^(t+1).
known = {}  # modulus exponent -> residue
bad = []
for n in range(2, N + 1):
    t = r[n]
    if t is None or t < 0:
        bad.append((n, t)); continue
    res = (n + (1 << t)) % (1 << (t + 1))
    # n determines alpha mod 2^(t+1) exactly
    known.setdefault(t + 1, set()).add(res)
# combine
maxe = max(known)
alpha = None
consistent = True
cur = 0
for e in range(1, maxe + 1):
    if e in known:
        if len(known[e]) > 1: consistent = False; print('CONFLICT at exponent', e, sorted(known[e])[:5])
        res = min(known[e])
        if alpha is not None and res % (1 << (e - 1)) != alpha % (1 << (e - 1)):
            consistent = False; print('CONFLICT lower bits at exponent', e, res, alpha)
        alpha = res
# full check against alpha mod 2^maxe
if alpha is not None:
    for n in range(2, N + 1):
        t = r[n]
        if t is None or t < 0: continue
        if t + 1 <= maxe:
            pass
        # check v2(n-alpha) mod 2^maxe equals t whenever t < maxe
        dd = (n - alpha) % (1 << maxe)
        vv = v2(dd) if dd else maxe
        if t < maxe and vv != t:
            consistent = False; print('MISMATCH n', n, 'r_n', t, 'v2(n-alpha mod 2^maxe)', vv); break
print('N', N, 'k', k, 'bad(negative or zero diff)', bad[:10], 'count', len(bad))
print('consistent', consistent, 'max exponent pinned', maxe)
if alpha is not None:
    print('alpha mod 2^%d =' % maxe, alpha, 'binary', bin(alpha))
print('r_n for n=2..40:', [r[n] for n in range(2, min(N, 40) + 1)])
