"""Exact-integer diagnostic for Xiong arXiv:1605.09135 Conjecture 3.1 (MathDB 333242).
h(q) = sum_{n>=1} (-1)^{n+1} q^{n(n+1)/2} / (1-q^n);  A_m(n) = [q^n] h(q^m)/(q)_inf.
Literal statement: [q^n] (p1 h(q^p1) - p2 h(q^p2))/(q)_inf = p1 A_p1(n) - p2 A_p2(n) > 0 (n >= p2).
Reversed (intended) reading: p2 A_p2(n) - p1 A_p1(n) > 0 for n >= p2.
usage: xiong.py PMAX N
"""
import sys
PMAX, N = int(sys.argv[1]), int(sys.argv[2])
# partition numbers p(0..N) by Euler pentagonal recurrence
p = [0] * (N + 1); p[0] = 1
for n in range(1, N + 1):
    s, k = 0, 1
    while True:
        g1 = k * (3 * k - 1) // 2
        if g1 > n: break
        sg = 1 if k % 2 else -1
        s += sg * p[n - g1]
        g2 = k * (3 * k + 1) // 2
        if g2 <= n: s += sg * p[n - g2]
        k += 1
    p[n] = s
# coefficients of h(q) up to N
h = [0] * (N + 1)
n = 1
while n * (n + 1) // 2 <= N:
    sg = 1 if n % 2 else -1
    e = n * (n + 1) // 2
    while e <= N:
        h[e] += sg; e += n
    n += 1
primes = [q for q in range(2, PMAX + 1) if all(q % d for d in range(2, int(q ** .5) + 1))]
A = {}
for m in primes:
    A[m] = [sum(h[i] * p[n - m * i] for i in range(1, n // m + 1)) for n in range(N + 1)]
lit_bad, rev_bad, rev_zero = 0, [], []
for a in range(len(primes)):
    for b in range(a):
        p1, p2 = primes[a], primes[b]
        lit = p1 * A[p1][p2] - p2 * A[p2][p2]
        assert lit == -p2, (p1, p2, lit)
        lit_bad += 1
        for n in range(1, N + 1):
            d = p2 * A[p2][n] - p1 * A[p1][n]
            if d < 0: rev_bad.append((p1, p2, n, d)); break
            if d == 0 and n >= p2: rev_zero.append((p1, p2, n))
print('primes', primes[0], '..', primes[-1], 'count', len(primes), 'N', N)
print('literal statement: coefficient at n=p2 equals -p2 for all', lit_bad, 'pairs (literal claim fails at n=p2)')
print('reversed reading: first negative coefficients:', rev_bad[:10], 'pairs failing', len(rev_bad))
print('reversed reading: zero coefficients at n>=p2:', rev_zero[:20], 'count', len(rev_zero))
