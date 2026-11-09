# Test explicit families of cyclic sequences of length n = 2b + rho:
#   S = e_0..e_{b-1}, w_1..w_R, e_t..e_{b-1}   (cyclic), w columns intervals.
import sys, json, os
sys.path.insert(0, os.path.dirname(__file__))
from offset import rank
def build(b, ivs, t):
    e = lambda i: [1 if k == i else 0 for k in range(b)]
    return [e(i) for i in range(b)] + [[1 if lo <= k <= hi else 0 for k in range(b)] for (lo, hi) in ivs] + [e(i) for i in range(t, b)]
def valid(S, b):
    n = len(S)
    return all(rank([S[(s + j) % n] for j in range(b)], b) == b for s in range(n))
def sliding(b, rho):  # R = rho, t = 0, columns [c, c+b-rho]
    return [(c, c + b - rho) for c in range(rho)], 0
B = int(sys.argv[1]); fails = []; ok = []
for b in range(2, B+1):
    for rho in range(1, b):
        ivs, t = sliding(b, rho)
        S = build(b, ivs, t)
        assert len(S) == 2*b + rho
        (ok if valid(S, b) else fails).append((b, rho))
print(json.dumps({'B': B, 'ok_count': len(ok), 'fails': fails[:60], 'nfails': len(fails)}))
