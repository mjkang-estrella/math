"""336718 exploration: test candidate positive recurrences for Q_j(m) (see qdiag.py).
Prints R = Q_j(m) - q[m-1] Q_{j-1}(m-1) and the exact quotient R / Q_{j-2}(m-2) if it divides."""
import sys
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


def divmod_poly(a, b):
    a = list(a)
    while len(b) > 1 and b[-1] == 0:
        b = b[:-1]
    if len(a) < len(b):
        return [0], a
    qd = [0] * (len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1]
        if c % b[-1]:
            return None, None
        c //= b[-1]
        qd[i] = c
        for k, y in enumerate(b):
            a[i + k] -= c * y
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return qd, a


def qint(m):
    return [1] * m if m > 0 else [0]


Q = {}
for m in range(0, NM + 1):
    Q[(0, m)] = [1]
for j in range(1, NM + 1):
    for m in range(j, NM + 1):
        Q[(j, m)] = add(mul(qint(m - j + 1), Q[(j - 1, m)]), Q[(j - 1, m - 1)] if (j - 1, m - 1) in Q else [0], -1)
for j in range(2, 7):
    for m in range(j, min(NM, j + 6) + 1):
        R = add(Q[(j, m)], mul([0] + qint(m - 1), Q[(j - 1, m - 1)]), -1)
        if Q[(j - 2, m - 2)] == [0]:
            print('j', j, 'm', m, 'R', R[:14], 'divisor zero')
            continue
        qd, rem = divmod_poly(R, Q[(j - 2, m - 2)])
        print('j', j, 'm', m, 'R', R[:14], 'quot', qd if rem == [0] else None)
