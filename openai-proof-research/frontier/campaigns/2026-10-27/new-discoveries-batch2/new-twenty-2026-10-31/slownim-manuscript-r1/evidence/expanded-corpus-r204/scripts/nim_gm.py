"""Exhaustive check of the GM-strategy (uniform) Nash equilibrium conjecture for exact slow NIM(n,n-1)
with l players (Gurvich-Naumova arXiv:2311.03257 Conj. 1 = arXiv:2312.08382 Conj. 1; MathDB 360653/361128).
Rules (source Sec. 'Game NIM(n,n-1) for l players'): position = non-negative n-vector (multiset);
a move keeps one entry and reduces the other n-1 entries by 1, legal only if those are positive;
terminal iff >= 2 entries are non-positive; the player to move at a terminal position loses;
loser pays C-L, each winner gets (C-L)/(l-1), C > every play length (so: win > lose; a winner prefers
shorter plays, a loser longer ones).  GM-move: keep the minimal entry that is a multiple of l
(ties irrelevant for multisets); if no entry is a multiple of l keep the largest entry.
usage: nim_gm.py n l B   (all initial positions with entries in [0,B], all deviating players)"""
import sys, itertools, functools, json
sys.setrecursionlimit(100000)
n, l, B = map(int, sys.argv[1:4])
def terminal(x): return sum(1 for v in x if v <= 0) >= 2
def moves(x):
    out = set()
    for i in range(n):
        if all(x[j] > 0 for j in range(n) if j != i):
            out.add(tuple(sorted(x[j] - (j != i) for j in range(n))))
    return out
def gm(x):
    mult = [v for v in x if v % l == 0]
    keep = min(mult) if mult else max(x)
    i = x.index(keep)
    return tuple(sorted(x[j] - (j != i) for j in range(n)))
@functools.lru_cache(None)
def glen(x):            # remaining length of the all-GM play
    return 0 if terminal(x) else 1 + glen(gm(x))
def key(win, r): return (1, -r) if win else (0, r)
@functools.lru_cache(None)
def best(x, p, d):      # p = index of player to move; d = deviator; returns (key, r, loser)
    if terminal(x): return (key(p != d, 0), 0, p)
    if p == d:
        cands = []
        for y in moves(x):
            k, r, los = best(y, (p + 1) % l, d)
            cands.append((key(los != d, r + 1), r + 1, los))
        return max(cands)
    k, r, los = best(gm(x), (p + 1) % l, d)
    return (key(los != d, r + 1), r + 1, los)
viol = []; checked = 0
for x in itertools.combinations_with_replacement(range(B + 1), n):
    if terminal(x): continue
    g = glen(x)
    for p in range(l):
        for d in range(l):
            checked += 1
            los = (p + g) % l
            gk = key(los != d, g)
            bk, br, blos = best(x, p, d)
            if bk > gk: viol.append(dict(x=x, mover=p, deviator=d, gm_len=g, gm_loser=los, br_len=br, br_loser=blos))
print(json.dumps(dict(n=n, l=l, B=B, checked=checked, violations=len(viol), first=viol[:5])))
