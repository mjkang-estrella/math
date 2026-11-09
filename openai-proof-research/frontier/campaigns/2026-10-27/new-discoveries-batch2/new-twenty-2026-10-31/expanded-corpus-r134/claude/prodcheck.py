import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# Product of antipodal pairs: blocks of sizes a_1..a_d; players eps in {0,1}^d at (eps_1 1^{a_1},...).
# All players equivalent by translation, so check player 0 only.
import time
from math import lcm
from vor import scores_lowmem
def run(blocks):
    n = sum(blocks); d = len(blocks); pos = []
    for e in range(1 << d):
        v = 0; off = 0
        for b, a in enumerate(blocks):
            if e >> b & 1: v |= ((1 << a) - 1) << off
            off += a
        pos.append(v)
    k = len(pos); L = lcm(*range(1, k + 1)); V = 1 << n
    S = scores_lowmem(n, pos, 0, L)
    cur = S[0]; best = max(S)
    return cur, best, S.index(best), L * V // k
for arg in sys.argv[1:]:
    blocks = list(map(int, arg.split(',')))
    t = time.time(); cur, best, q, fair = run(blocks)
    print(blocks, 'n', sum(blocks), 'cur/fair', cur, fair, 'best', best, 'argbest', bin(q), 'EQ' if best <= cur else 'NOT', round(time.time() - t, 1), flush=True)
