# Validation at small n: brute force over every player, every target vertex and every voter,
# compared with the all-v convolution method; reports max deviation score per profile.
import sys; sys.path.insert(0, 'scripts')
from vk import *
import itertools, random
def full(m):
    n = sum(m); P = positions(m); best = []
    for i in range(8):
        others = [P[j] for j in range(8) if j != i]
        tab = voter_table(n, others)
        cur = score_brute(n, others, P[i], tab)
        S = scores_all(n, others)
        for v in range(1 << n):
            assert S[v] == score_brute(n, others, v, tab), (m, i, v)
        best.append((cur, int(S.max()), int(S.argmax())))
    return n, best
random.seed(1)
cases = [(2,1,1,1,1,1,1), (1,1,1,1,1,1,1), (1,1,1,0,0,0,0), (2,2,2,1,1,1,1), (3,1,1,1,0,0,0), (1,1,1,1,4,0,0)]
for _ in range(4):
    cases.append(tuple(random.randint(0, 2) for _ in range(7)))
for m in cases:
    if sum(m) > 10 or sum(m) < 3: continue
    n, best = full(m)
    cur = {frac(b[0], n) for b in best}
    mx = max(frac(b[1], n) for b in best)
    print('m', m, 'n', n, 'current scores', sorted(cur), 'max deviation score', mx, 'EQ' if mx <= max(cur) and len(cur) == 1 and mx == Fraction(1,8) else 'NOT', flush=True)
print('all brute == convolution checks passed')
