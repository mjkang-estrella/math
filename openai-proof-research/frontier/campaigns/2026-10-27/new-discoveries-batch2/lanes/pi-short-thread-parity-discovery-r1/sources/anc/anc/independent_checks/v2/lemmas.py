"""Numerical check of Lemmas L1-L5 (Section 9) with the independent solver spider.py."""
import sys
from spider import G, Gamma, norm

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
YMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 24
D2 = ('I', 'O')
bad = {k: 0 for k in ['L1', 'L2', 'L2free', 'L3', 'L4', 'L5', 'L5floor', 'f']}


def report(tag, msg):
    bad[tag] += 1
    if bad[tag] <= 5:
        print(tag, 'FAIL', msg)


def S(j, b):
    return (b & (j - 1)) == 0


# L1
for k in range(1, KMAX + 1):
    for i in range(1, KMAX + 1):
        for a in D2:
            for b in D2:
                v = G('i', (k, a), (i, b))
                if (k, a) == (1, 'O'):
                    e = i ^ 1
                elif (i, b) == (1, 'O'):
                    e = k ^ 1
                else:
                    e = (k + i + (a == b)) % 2
                if v != e:
                    report('L1', (k, a, i, b, v, e))
print('L1 done', bad['L1'])

# L2
for i in range(1, KMAX + 1):
    gi = G('i', (1, 'F'), (i, 'I'))
    go = G('i', (1, 'F'), (i, 'O'))
    ei = i - 1 if i % 4 == 3 else i + 1
    eo = i - 1 if i % 4 == 1 else i + 1
    if (gi, go) != (ei, eo):
        report('L2', (i, gi, go, ei, eo))
    gf = G('i', (1, 'F'), (i, 'F'))
    if gf != (i + 1) % 2:
        report('L2free', (i, gf))
    # also the 'o' versions by reversal claim
    if G('o', (1, 'F'), (i, 'F')) != gf:
        report('f', ('o-version', i))
print('L2 done', bad['L2'], bad['L2free'])

# L3
for y in range(2, YMAX + 1, 2):
    for i in range(1, KMAX + 1):
        for b in D2:
            v = G('i', (y, 'F'), (i, b))
            if (i, b) == (1, 'I'):
                e = y + 1
            elif (i, b) == (1, 'O'):
                e = 1
            else:
                e = y - 2 + (i + (b == 'I')) % 2
            if v != e:
                report('L3', (y, i, b, v, e))
print('L3 done', bad['L3'])

# L4
for k in range(1, KMAX + 1):
    for i in range(1, KMAX + 1):
        for a in D2:
            for b in D2:
                v = G('n', (1, 'F'), (k, a), (i, b))
                if k == 1 and i == 1 and a == b:
                    e = 3
                else:
                    e = (k + i + (a != b)) % 2
                if v != e:
                    report('L4', (k, a, i, b, v, e))
print('L4 done', bad['L4'])

# L5
for j in range(1, YMAX // 2 + 1):
    y = 2 * j
    for i in range(1, KMAX + 1):
        if i % 2 == 1 and S(j, (i - 1) // 2):
            eps = -1
        elif i % 2 == 0 and S(j, i // 2):
            eps = 1
        else:
            eps = 0
        for d in D2:
            v = G('n', (1, 'F'), (y, 'F'), (i, d))
            if v != i + y - 2 + eps:
                report('L5', (j, i, d, v, i + y - 2 + eps))
            if v // 2 != i // 2 + j - 1:
                report('L5floor', (j, i, d, v))
print('L5 done', bad['L5'], bad['L5floor'])
print('SUMMARY', bad)
