import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Fully independent brute-force equilibrium check (no WHT, no symmetry): every player, every deviation.
from fractions import Fraction
from subspace import profile
d = int(sys.argv[1]); mult = list(map(int, sys.argv[2].split(',')))
n, pos = profile(d, mult); V = 1 << n; k = len(pos)
pc = [bin(x).count('1') for x in range(V)]
def score(P, i):
    s = 0
    for x in range(V):
        ds = [pc[x ^ p] for p in P]; m = min(ds)
        if ds[i] == m: s += 840 // ds.count(m)
    return s
ok = True; worst = None
for i in range(k):
    cur = score(pos, i)
    for q in range(V):
        P = list(pos); P[i] = q
        sc = score(P, i)
        if sc > cur:
            ok = False; worst = (i, q, cur, sc); break
    if not ok: break
print('n', n, 'k', k, 'mult', mult, 'positions', pos, 'equilibrium', ok, worst)
