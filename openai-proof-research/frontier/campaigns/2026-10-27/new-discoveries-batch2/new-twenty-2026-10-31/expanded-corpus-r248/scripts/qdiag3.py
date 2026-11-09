"""336718 exploration: F(m,j) = sum_i (-1)^i C(j,i) [m-i]!_q.  Classical D(m,j) = m D(m-1,j) + j D(m-2,j-1).
Print R(m,j) = F(m,j) - [m] F(m-1,j) and test R against shifted multiples of F(m-2,j-1) and F(m-1,j-1)."""
import sys
from math import comb
NM = int(sys.argv[1])


def add(a, b, s=1):
    n = max(len(a), len(b))
    r = [0] * n
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += s * x
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def qint(m):
    return [1] * m if m > 0 else [0]


def sh(a, k):
    return [0] * k + a


fact = [[1]]
for m in range(1, NM + 1):
    fact.append(mul(fact[-1], qint(m)))
F = {}
for m in range(0, NM + 1):
    for j in range(0, m + 1):
        P = [0]
        for i in range(j + 1):
            P = add(P, [comb(j, i) * c for c in fact[m - i]], 1 if i % 2 == 0 else -1)
        F[(m, j)] = P
for j in range(1, 5):
    for m in range(j + 1, j + 6):
        R = add(F[(m, j)], mul(qint(m), F[(m - 1, j)]), -1)
        G = F[(m - 2, j - 1)]
        # try R = sum_t c_t q^t G : polynomial division
        print('j', j, 'm', m, 'R', R, '\n      G=F(m-2,j-1)', G)
