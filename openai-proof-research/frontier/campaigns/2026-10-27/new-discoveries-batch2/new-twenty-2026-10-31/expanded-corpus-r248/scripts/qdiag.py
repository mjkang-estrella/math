"""336718 (Lewis-Morales arXiv:1707.08192v2, Conjecture conj:poscompdiag): explore
P_n(q) = sum_{i=0}^n (-1)^i C(n,i) [2n-i]!_q  (M_{2n}(complement I_v, q) = q^{2n(n-1)} P_n(q), source Cor. fullrankrect)
and Q_j(m) := sum_i (-1)^i C(j,i) [m-i]!_q / [m-j]!_q (exact division), recursion Q_j(m) = [m-j+1]Q_{j-1}(m) - Q_{j-1}(m-1).
usage: qdiag.py NMAX  -> prints positivity of P_n, and table of sign of Q_j(m) for j<=m<=2*NMAX"""
import sys
from math import comb
NMAX = int(sys.argv[1])


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
    return r


def qint(m):
    return [1] * m if m > 0 else [0]


M = 2 * NMAX
fact = [[1]]
for m in range(1, M + 1):
    fact.append(mul(fact[-1], qint(m)))
# P_n
allpos = True
for n in range(1, NMAX + 1):
    P = [0]
    for i in range(n + 1):
        P = add(P, [comb(n, i) * c for c in fact[2 * n - i]], 1 if i % 2 == 0 else -1)
    neg = [k for k, c in enumerate(P) if c < 0]
    if neg:
        allpos = False
    if n <= 6 or neg:
        print('n', n, 'P_n(1)', sum(P), 'neg coeffs at', neg[:10], 'first coeffs', P[:12])
print('P_n in N[q] for all n <=', NMAX, ':', allpos)
# Q table
Q = {}
for m in range(0, M + 1):
    Q[(0, m)] = [1]
for j in range(1, M + 1):
    for m in range(j, M + 1):
        Q[(j, m)] = add(mul(qint(m - j + 1), Q[(j - 1, m)]), Q[(j - 1, m - 1)] if (j - 1, m - 1) in Q else [0], -1)
print('Q_j(m) nonnegative? rows j, columns m=j..min(2NMAX, j+12)')
for j in range(1, min(M, 14) + 1):
    row = []
    for m in range(j, min(M, j + 12) + 1):
        row.append('+' if all(c >= 0 for c in Q[(j, m)]) else '-')
    print(j, ''.join(row))
for (j, m) in [(1, 2), (2, 4), (3, 6), (2, 3), (3, 5)]:
    print('Q', j, m, Q[(j, m)])
