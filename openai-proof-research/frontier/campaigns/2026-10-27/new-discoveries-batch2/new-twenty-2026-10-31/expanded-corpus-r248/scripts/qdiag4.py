"""336718: Q_j(m) = sum_i (-1)^i C(j,i) [m-i][m-i-1]...[m-j+1]  (q-count of fixed-point-free injections [j]->[m]).
Classical I(m,j) = I(m-1,j) + j I(m-1,j-1).  Test q-analogue Q_j(m) - q^a Q_j(m-1) = B * Q_{j-1}(m-1) for a in 0..3,
printing the exact quotient B when it exists."""
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


def pdiv(a, b):
    a = list(a)
    while len(b) > 1 and b[-1] == 0:
        b = b[:-1]
    if b == [0]:
        return None
    # strip common low zeros
    if len(a) < len(b):
        return None if any(a) else [0]
    qd = [0] * (len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1]
        if c % b[-1]:
            return None
        c //= b[-1]
        qd[i] = c
        for k, y in enumerate(b):
            a[i + k] -= c * y
    return qd if not any(a) else None


def qint(m):
    return [1] * m if m > 0 else [0]


def falling(m, k):
    r = [1]
    for t in range(k):
        r = mul(r, qint(m - t))
    return r


Q = {}
for m in range(0, NM + 1):
    for j in range(0, m + 1):
        P = [0]
        for i in range(j + 1):
            P = add(P, [comb(j, i) * c for c in falling(m - i, j - i)], 1 if i % 2 == 0 else -1)
        Q[(j, m)] = P
for j in range(1, 6):
    for m in range(j + 1, j + 6):
        out = []
        for a in range(0, 4):
            R = add(Q[(j, m)], [0] * a + Q[(j, m - 1)], -1)
            B = pdiv(R, Q[(j - 1, m - 1)])
            out.append((a, B))
        print('j', j, 'm', m, ' '.join(f'a={a}:{B}' for a, B in out))
