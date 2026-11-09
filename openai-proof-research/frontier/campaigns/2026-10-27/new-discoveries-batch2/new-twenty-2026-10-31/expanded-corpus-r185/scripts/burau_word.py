"""Compute contiguous principal Burau minors' degree ranges for a specific e-homogeneous word. Usage: burau_word.py e w1,w2,..."""
import sys, pathlib, itertools
es = sys.argv[1]; w = [int(x) for x in sys.argv[2].split(',')]
e = [1 if c == '+' else -1 for c in es]; n = len(e) + 1
def padd(p, q):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + v
        if r[k] == 0: del r[k]
    return r
def pmul(p, q):
    r = {}
    for a, x in p.items():
        for c, y in q.items(): r[a + c] = r.get(a + c, 0) + x * y
    return {k: v for k, v in r.items() if v}
def gen(i, s):
    M = [[({0: 1} if a == c else {}) for c in range(n)] for a in range(n)]; a = i - 1
    if s == 1: M[a][a] = {0: 1, 1: -1}; M[a][a + 1] = {1: 1}; M[a + 1][a] = {0: 1}; M[a + 1][a + 1] = {}
    else: M[a][a] = {}; M[a][a + 1] = {0: 1}; M[a + 1][a] = {-1: 1}; M[a + 1][a + 1] = {0: 1, -1: -1}
    return M
def mmul(A, B):
    R = [[{} for _ in range(n)] for _ in range(n)]
    for r in range(n):
        for c in range(n):
            acc = {}
            for k in range(n):
                if A[r][k] and B[k][c]: acc = padd(acc, pmul(A[r][k], B[k][c]))
            R[r][c] = acc
    return R
def det(Mx):
    k = len(Mx); tot = {}
    for perm in itertools.permutations(range(k)):
        sgn = 1
        for i in range(k):
            for j in range(i + 1, k):
                if perm[i] > perm[j]: sgn = -sgn
        term = {0: sgn}
        for i in range(k):
            term = pmul(term, Mx[i][perm[i]])
            if not term: break
        if term: tot = padd(tot, term)
    return tot
M = [[({0: 1} if a == c else {}) for c in range(n)] for a in range(n)]
for i in w: M = mmul(M, gen(i, e[i - 1]))
print('word', w)
for lo in range(n):
    for hi in range(lo + 1, n + 1):
        d = det([row[lo:hi] for row in M[lo:hi]])
        print((lo, hi), 'maxdeg', max(d) if d else None, 'mindeg', min(d) if d else None, 'top coeff', d[max(d)] if d else None)
