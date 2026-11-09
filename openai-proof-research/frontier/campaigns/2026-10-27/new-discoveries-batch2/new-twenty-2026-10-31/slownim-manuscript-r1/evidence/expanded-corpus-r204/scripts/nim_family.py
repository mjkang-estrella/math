"""Check candidate violation families for exact slow NIM(n,n-1), l players (rules as nim_gm.py, literal GM convention),
exploring only positions reachable from the given start.  Family L2W(n,l): x = ((n-2)l+1 [n-1 times], (n-1)l-1),
player 0 to move, deviator 0.  Family SHORTfree(n,l) is searched separately.  Also records a one-deviation witness:
whether 'deviate only at the first move, then GM' already suffices, and which first move.
usage: nim_family.py nmax lmax"""
import sys, functools, json
sys.setrecursionlimit(1000000)
NM, LM = int(sys.argv[1]), int(sys.argv[2])
out = []
for n in range(3, NM + 1):
  for l in range(3, LM + 1):
    def terminal(x): return sum(1 for v in x if v <= 0) >= 2
    def moves(x):
        o = set()
        for i in range(n):
            if all(x[j] > 0 for j in range(n) if j != i):
                o.add(tuple(sorted(x[j] - (j != i) for j in range(n))))
        return sorted(o)
    def gm(x):
        mult = [v for v in x if v % l == 0]
        keep = min(mult) if mult else max(x)
        i = x.index(keep)
        return tuple(sorted(x[j] - (j != i) for j in range(n)))
    def gmplay(x, p):
        L = 0
        while not terminal(x): x = gm(x); L += 1
        return L, (p + L) % l
    x0 = tuple(sorted([(n - 2) * l + 1] * (n - 1) + [(n - 1) * l - 1]))
    g, los = gmplay(x0, 0)
    # one-shot deviations at the first move
    one = []
    for y in moves(x0):
        L, lo = gmplay(y, 1)
        one.append(dict(first_move_to=y, len=L + 1, loser=lo))
    good = [o for o in one if o['loser'] != 0]
    out.append(dict(n=n, l=l, x0=x0, gm_len=g, gm_loser=los, gm_first_move=gm(x0), one_shot_wins=good))
    print(json.dumps(out[-1]), flush=True)
