import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Family: line functionals f=1,2,3 with multiplicities (a,b,c), external f=4 with multiplicity d.
import time
from subspace import check
nmin, nmax, dd = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
t0 = time.time()
for n in range(nmin, nmax + 1):
    eq = []; no = []
    s = n - dd
    for a in range(s + 1):
        for b in range(a + 1):
            c = s - a - b
            if c < 0 or c > b: continue
            mult = [a, b, c, dd, 0, 0, 0]
            nn, cur, best, arg, fair = check(3, mult)
            (eq if best <= cur else no).append((a, b, c))
    print('n', n, 'd', dd, 'EQ', eq, 'NOT', no, round(time.time() - t0, 1), flush=True)
