# Berczi (arXiv:2603.06692v1) Conjecture 7 (MathDB 373480), first clause:
# every Latin square of even order n has, in the row, column or symbol view, a pair of lines whose
# induced matching permutation has an odd cycle.
# Views: row view of L; row view of L^T; row view of the conjugate S[s][c] = r iff L[r][c] = s.
# The property "no odd cycle in any view" is invariant under isotopy (perms are conjugated) and
# under conjugation (views permuted), so reduced squares cover all main classes.
# usage: latintrade.py n [maxreport]
import sys, itertools

def cycles_have_odd(p1, p2, n):
    # p1, p2: lists line->index map; permutation pi(c)=c' with p2[c'] == p1[c]
    pos2 = [0] * n
    for c in range(n): pos2[p2[c]] = c
    pi = [pos2[p1[c]] for c in range(n)]
    seen = [False] * n
    for s in range(n):
        if seen[s]: continue
        l = 0; x = s
        while not seen[x]: seen[x] = True; x = pi[x]; l += 1
        if l % 2: return True
    return False

def views(L, n):
    T = [[L[r][c] for r in range(n)] for c in range(n)]
    S = [[0] * n for _ in range(n)]
    for r in range(n):
        for c in range(n): S[L[r][c]][c] = r
    return (L, T, S)

def has_odd_trade(L, n):
    for M in views(L, n):
        for i in range(n):
            for j in range(i + 1, n):
                if cycles_have_odd(M[i], M[j], n): return True
    return False

def reduced_squares(n):
    L = [[-1] * n for _ in range(n)]
    for c in range(n): L[0][c] = c
    for r in range(n): L[r][0] = r
    rowused = [set([r]) for r in range(n)]; colused = [set([c]) for c in range(n)]
    rowused[0] = set(range(n))
    cells = [(r, c) for r in range(1, n) for c in range(1, n)]
    def rec(i):
        if i == len(cells):
            yield [row[:] for row in L]; return
        r, c = cells[i]
        for s in range(n):
            if s in rowused[r] or s in colused[c]: continue
            L[r][c] = s; rowused[r].add(s); colused[c].add(s)
            yield from rec(i + 1)
            rowused[r].discard(s); colused[c].discard(s); L[r][c] = -1
    yield from rec(0)

if __name__ == '__main__':
    n = int(sys.argv[1])
    cnt = 0; bad = []
    for L in reduced_squares(n):
        cnt += 1
        if not has_odd_trade(L, n):
            bad.append(L)
            if len(bad) <= 5: print('NO ODD-CYCLE TRADE IN ANY VIEW:', L, flush=True)
    print('n', n, 'reduced squares', cnt, 'without odd-cycle trade', len(bad))
