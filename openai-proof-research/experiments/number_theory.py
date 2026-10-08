"""Diagnostics for number_theory.md; no numerical output is used as proof.

Run: python openai-proof-research/experiments/number_theory.py
"""
from fractions import Fraction as Q
from math import log, sin, gamma, sqrt, pi


def rising(a, n):
    out = Q(1)
    for j in range(n):
        out *= a + j
    return out


def moment(exponents):
    out = Q(1)
    for k in exponents:
        out *= rising(Q(1, 4), k)
    return out / rising(Q(1), sum(exponents))


def multiply(a, b):
    out = {}
    for x, c in a.items():
        for y, d in b.items():
            z = tuple(u + v for u, v in zip(x, y))
            out[z] = out.get(z, Q(0)) + c * d
    return out


def expect(poly):
    return sum(c * moment(x) for x, c in poly.items())


x = {(0, 0, 0, 0): Q(-1, 2), (1, 0, 0, 0): Q(1),
     (0, 1, 0, 0): Q(1)}
y = {(0, 0, 0, 0): Q(-1, 2), (1, 0, 0, 0): Q(1),
     (0, 0, 1, 0): Q(1)}
x2, y2 = multiply(x, x), multiply(y, y)
assert expect(x2) == Q(1, 8)
assert expect(multiply(x, y)) == 0
assert expect(multiply(x2, y2)) == Q(7, 384)
assert expect(multiply(x2, y2)) - expect(x2) * expect(y2) == Q(1, 384)
print('Exact Dirichlet checks: variance=1/8, covariance=0, '
      'mixed centered squares=7/384, covariance of squares=1/384')

limit = 1_000_000
spf = list(range(limit + 1))
for p in range(2, int(sqrt(limit)) + 1):
    if spf[p] == p:
        for n in range(p * p, limit + 1, p):
            if spf[n] == n:
                spf[n] = p

count = 0
sum_v = sum_v2 = sum_g = 0.0
for p in range(3, limit + 1):
    if spf[p] != p:
        continue
    n = p - 1
    log_n = log(n)
    v = g = 0.0
    while n > 1:
        q, e = spf[n], 0
        while n % q == 0:
            n //= q
            e += 1
        w = log(q) / log_n
        v += e * (e + 2) * w * w / 12
        g += e * (2 * e + 1) * w / (6 * (e + 1))
    count += 1
    sum_v += v
    sum_v2 += v * v
    sum_g += g
print(f'Primes 3..{limit}: {count}; exact conditional divisor moments averaged')
print(f'  E variance={sum_v/count:.8f} (limit .125)')
print(f'  E variance^2={sum_v2/count:.8f} (limit {7/384:.8f})')
print(f'  E log(gcd)/log(p-1)={sum_g/count:.8f} (limit .25)')

b = 0.5
constant = gamma((1-b)/2) / (sqrt(pi)*gamma(1-b/2))
for n in [10_000, 100_000, 1_000_000]:
    avg = sum(abs(sin(j)) ** (-b) for j in range(1, n+1)) / n
    print(f'b={b}, N={n}: sine inverse moment={avg:.8f}; limit={constant:.8f}')
