"""Classify GM-equilibrium violations (see nim_gm.py for rules). Types:
 L2W = deviator loses under GM but can force a win; LONG = loses either way but can lengthen the play;
 SHORT = wins under GM and can win with a shorter play.  Also reports the minimal-sum violation.
usage: nim_classify.py n l B"""
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
def glen(x): return 0 if terminal(x) else 1 + glen(gm(x))
def key(win, r): return (1, -r) if win else (0, r)
@functools.lru_cache(None)
def best(x, p, d):
    if terminal(x): return (key(p != d, 0), 0, p)
    nxt = moves(x) if p == d else [gm(x)]
    c = []
    for y in nxt:
        k, r, los = best(y, (p + 1) % l, d)
        c.append((key(los != d, r + 1), r + 1, los))
    return max(c)
cnt = {'L2W': 0, 'LONG': 0, 'SHORT': 0}; first = {}; tot = 0; pos_viol = set()
for x in sorted(itertools.combinations_with_replacement(range(B + 1), n), key=lambda t: (sum(t), t)):
    if terminal(x): continue
    g = glen(x)
    for p in range(l):
        for d in range(l):
            tot += 1
            los = (p + g) % l; gk = key(los != d, g)
            bk, br, bl = best(x, p, d)
            if bk > gk:
                t = 'L2W' if los == d and bl != d else ('LONG' if los == d else 'SHORT')
                cnt[t] += 1; pos_viol.add(x)
                first.setdefault(t, dict(x=x, mover=p, deviator=d, gm_len=g, gm_loser=los, br_len=br, br_loser=bl))
print(json.dumps(dict(n=n, l=l, B=B, checked=tot, positions_with_violation=len(pos_viol), counts=cnt, first_by_type=first)))
