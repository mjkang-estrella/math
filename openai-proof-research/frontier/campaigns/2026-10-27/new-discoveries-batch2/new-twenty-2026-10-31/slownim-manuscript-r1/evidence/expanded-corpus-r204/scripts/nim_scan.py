"""Scan GM-equilibrium violations for exact slow NIM(n,n-1), l players (rules as in nim_gm.py).
mode 'lit'  : GM convention of the source (no multiple of l -> keep the largest entry).
mode 'adv'  : convention-free -- whenever a non-deviating player faces a position with no multiple of l,
              that move is chosen adversarially against the deviator (worst legal move); a violation in
              this mode holds for every completion of the GM-rule.
Reports, per (n,l), the number of initial positions (player 0 to move, entries <= B) where some player
has a profitable deviation, by type (L2W = loser can force a win), and the lexicographically smallest
(sum, x) L2W witness.  usage: nim_scan.py mode B n1,n2,.. l1,l2,.."""
import sys, itertools, functools, json
sys.setrecursionlimit(100000)
mode = sys.argv[1]; B = int(sys.argv[2])
NS = [int(t) for t in sys.argv[3].split(',')]; LS = [int(t) for t in sys.argv[4].split(',')]
res = []
for n in NS:
  for l in LS:
    def terminal(x): return sum(1 for v in x if v <= 0) >= 2
    def moves(x):
        out = set()
        for i in range(n):
            if all(x[j] > 0 for j in range(n) if j != i):
                out.add(tuple(sorted(x[j] - (j != i) for j in range(n))))
        return sorted(out)
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
        if p == d: nxt, agg = moves(x), max
        elif mode == 'adv' and not any(v % l == 0 for v in x): nxt, agg = moves(x), min
        else: nxt, agg = [gm(x)], max
        c = []
        for y in nxt:
            k, r, los = best(y, (p + 1) % l, d)
            c.append((key(los != d, r + 1), r + 1, los))
        return agg(c)
    cnt = {'L2W': 0, 'LONG': 0, 'SHORT': 0}; first = {}; npos = 0; nviol = 0
    for x in sorted(itertools.combinations_with_replacement(range(B + 1), n), key=lambda t: (sum(t), t)):
        if terminal(x): continue
        if mode == 'adv' and not any(v % l == 0 for v in x): continue
        npos += 1; g = glen(x); hit = False
        for d in range(l):
            los = g % l; gk = key(los != d, g)
            bk, br, bl = best(x, 0, d)
            if bk > gk:
                t = 'L2W' if los == d and bl != d else ('LONG' if los == d else 'SHORT')
                cnt[t] += 1; hit = True
                first.setdefault(t, dict(x=x, deviator=d, gm_len=g, gm_loser=los, br_len=br, br_loser=bl))
        nviol += hit
    res.append(dict(n=n, l=l, B=B, mode=mode, initial_positions=npos, positions_with_violation=nviol, counts=cnt, first=first))
    best.cache_clear(); glen.cache_clear()
    print(json.dumps(res[-1]), flush=True)
