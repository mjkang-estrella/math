"""Print the all-GM play and the one-shot deviation play for exact slow NIM(n,n-1) with l players
from x0 = ((n-2)l+1 [n-1 times], (n-1)l-1).  usage: nim_trace.py n l [dev_keep_value]"""
import sys
n, l = int(sys.argv[1]), int(sys.argv[2])
def terminal(x): return sum(1 for v in x if v <= 0) >= 2
def gmkeep(x):
    mult = [v for v in x if v % l == 0]
    return min(mult) if mult else max(x)
def step(x, keep):
    i = x.index(keep); return tuple(sorted(x[j] - (j != i) for j in range(n)))
def play(x, first_keep=None):
    rows = []; t = 0
    while not terminal(x):
        k = first_keep if (t == 0 and first_keep is not None) else gmkeep(x)
        rows.append((t, t % l, x, k)); x = step(x, k); t += 1
    rows.append((t, t % l, x, None)); return rows
a, b = (n - 2) * l + 1, (n - 1) * l - 1
x0 = tuple(sorted([a] * (n - 1) + [b]))
for name, fk in (('GM', None), ('deviation keep a', a)):
    r = play(x0, fk); print(name, 'length', r[-1][0], 'loser player', r[-1][1])
    for t, p, x, k in r: print('  t=%d player=%d x=%s keep=%s' % (t, p, x, k))
