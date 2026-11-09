import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Independent brute force: every player, every deviation, every voter; reports max deviation score.
import time
from subspace import profile
d = int(sys.argv[1]); mult = list(map(int, sys.argv[2].split(',')))
n, pos = profile(d, mult); V = 1 << n; k = len(pos)
pc = [bin(x).count('1') for x in range(V)]
L = 840
calls = 0
def score(P, i):
    global calls; calls += 1
    s = 0
    for x in range(V):
        ds = [pc[x ^ p] for p in P]; m = min(ds)
        if ds[i] == m: s += L // ds.count(m)
    return s
t = time.time(); res = []
for i in range(k):
    cur = score(pos, i); best = -1; arg = None
    for q in range(V):
        P = list(pos); P[i] = q
        sc = score(P, i)
        if sc > best: best, arg = sc, q
    res.append((i, cur, best, arg))
print('n', n, 'mult', mult, 'calls', calls, 'time', round(time.time() - t, 2))
for r in res: print('player', r[0], 'current', r[1], 'best deviation', r[2], 'at', r[3], 'fair share', L * V // k)
print('EQUILIBRIUM' if all(r[2] <= r[1] for r in res) else 'NOT EQUILIBRIUM')
