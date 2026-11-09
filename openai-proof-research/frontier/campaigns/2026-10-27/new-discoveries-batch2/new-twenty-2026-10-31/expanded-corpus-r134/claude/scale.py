import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import time
from subspace import check
f = int(sys.argv[1])
for arg in sys.argv[2:]:
    m = list(map(int, arg.split(',')))
    mm = [f * x for x in m]
    t = time.time(); n, cur, best, q, fair = check(3, mm)
    print(m, 'x', f, '->', mm, 'n', n, 'EQ' if best <= cur else 'NOT', 'rel_gain', (best - cur) / cur, 'argbest', bin(q), round(time.time() - t, 1), flush=True)
