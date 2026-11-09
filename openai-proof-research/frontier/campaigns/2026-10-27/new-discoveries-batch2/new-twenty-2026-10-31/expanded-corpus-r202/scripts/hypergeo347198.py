"""347198: exact check of the Barrott-Nabijou combinatorial identity (Conjecture 6.12, arXiv:2007.05016)
by direct partition sum, and of the Lagrange-inversion route: LHS = [x^d] exp(2d A(x)) / (2 d^2),
A(x) = sum_m (-1)^(m-1) binom(3m,m)/m x^m = -3 log B(-x), B = 1 + x B^3. usage: hypergeo347198.py DMAX"""
import sys
from fractions import Fraction as F
from math import comb, factorial
from collections import Counter
DMAX = int(sys.argv[1])

def partitions(n, m=None):
    if m is None: m = n
    if n == 0: yield []; return
    for k in range(min(n, m), 0, -1):
        for p in partitions(n - k, k): yield [k] + p

def lhs(d):
    s = F(0)
    for p in partitions(d):
        r = len(p); aut = 1
        for c in Counter(p).values(): aut *= factorial(c)
        t = F(2 ** (r - 1)) * F(d) ** (r - 2) / aut
        for di in p: t *= F((-1) ** (di - 1) * comb(3 * di, di), di)
        s += t
    return s

def via_exp(d):  # [x^d] exp(2d A) by power-series exponential, exact rationals
    a = [F(0)] + [F((-1) ** (m - 1) * comb(3 * m, m), m) * 2 * d for m in range(1, d + 1)]
    e = [F(1)] + [F(0)] * d
    for n in range(1, d + 1):  # e' = a' e
        e[n] = sum(k * a[k] * e[n - k] for k in range(1, n + 1)) / n
    return e[d] / (2 * d * d)

bad = []
for d in range(1, DMAX + 1):
    L = lhs(d); R = F(comb(4 * d - 1, d), d * d); X = via_exp(d)
    if not (L == R == X): bad.append((d, str(L), str(R), str(X)))
print('checked d = 1..%d; mismatches:' % DMAX, bad)
