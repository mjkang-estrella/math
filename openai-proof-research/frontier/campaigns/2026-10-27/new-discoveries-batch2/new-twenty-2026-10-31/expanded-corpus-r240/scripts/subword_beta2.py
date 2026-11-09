"""Faster check of Sundaram Conjecture 1 (346999) as polynomial positivity, via the transfer form
beta(T) = (-1)^m h(0),  h(j) = 1 - sum_{k>j} A(t_j, t_k) h(k),  t_0 = 0,
A(a,b) = sum_{i=0}^{b-a} C(b,i) x^i.  Cross-checked against subword_beta.py for small K.
Usage: subword_beta2.py KMIN KMAX   (checks all T with max(T) in [KMIN, KMAX])"""
import sys, itertools
from math import comb
K0, K1 = int(sys.argv[1]), int(sys.argv[2])
def mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r
def A(a, b): return [comb(b, i) for i in range(b - a + 1)]
def beta(T):
    t = (0,) + tuple(T); m = len(T)
    h = [None] * (m + 1)
    for j in range(m, -1, -1):
        acc = [1]
        for k in range(j + 1, m + 1):
            p = mul(A(t[j], t[k]), h[k])
            if len(p) > len(acc): acc += [0] * (len(p) - len(acc))
            for i, c in enumerate(p): acc[i] -= c
        h[j] = acc
    b = [(-1) ** m * c for c in h[0]]
    while len(b) > 1 and b[-1] == 0: b.pop()
    return b
neg = 0; cnt = 0; lowdeg_ok = True; minlead = None
for mx in range(K0, K1 + 1):
    for rest in itertools.product([0, 1], repeat=mx - 1):
        T = tuple([i + 1 for i in range(mx - 1) if rest[i]] + [mx])
        b = beta(T); cnt += 1
        if any(c < 0 for c in b):
            neg += 1
            if neg <= 20: print('NEG', T, b)
        # lowest nonzero degree
        ld = next(i for i, c in enumerate(b) if c)
        if ld != len(T): lowdeg_ok = False
        if len(b) - 1 != mx: print('degree anomaly', T, b)
print('range', K0, K1, 'sets', cnt, 'negative', neg, 'lowest degree == |T| always:', lowdeg_ok)
print('sample', (1, 3, 5), beta((1, 3, 5)), (2, 4), beta((2, 4)), (1, 4), beta((1, 4)))
