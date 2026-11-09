"""371239 diagnostic: Conjecture 5.2 of arXiv:2510.26664 in Z_p (p prime, d = 1).
Q_k(A) = #{(x,h_1..h_k) in Z_N^{k+1}: x + w.h in A for all w in {0,1}^k} = N^{k+1} ||1_A||_{U^k}^{2^k}.
Conjecture <=> |E|^{k+1} Q_k(Sigma) >= N^{k+1}.
For p prime, Chebotarev/Tao: for every nonempty Sigma there is f with |supp f| = p+1-|Sigma| and supp fhat = Sigma.
We report, for each k, the minimum over Sigma of ratio (p+1-|Sigma|)^{k+1} Q_k(Sigma) / p^{k+1}.
Exact integers only. usage: gowers_prime.py p kmax
"""
import sys
from functools import lru_cache
from fractions import Fraction

p = int(sys.argv[1]); kmax = int(sys.argv[2])
full = (1 << p) - 1

def shift(A, h):  # A - h  = {a - h}
    h %= p
    return ((A >> h) | (A << (p - h))) & full

@lru_cache(maxsize=None)
def Q(A, k):
    if k == 0:
        return bin(A).count('1')
    return sum(Q(A & shift(A, h), k - 1) for h in range(p))

def canon(A):
    best = None
    for t in range(p):
        B = shift(A, t)
        for a in range(1, p):
            C = 0
            for i in range(p):
                if B >> i & 1:
                    C |= 1 << (a * i % p)
            if best is None or C < best:
                best = C
    return best

reps = sorted({canon(A) for A in range(1, full + 1)})
for k in range(2, kmax + 1):
    best = None
    for A in reps:
        s = bin(A).count('1')
        e = p + 1 - s
        num = e ** (k + 1) * Q(A, k)
        r = Fraction(num, p ** (k + 1))
        if best is None or r < best[0]:
            best = (r, A, s, e, Q(A, k))
    r, A, s, e, q = best
    print(f'p={p} k={k} min ratio={float(r):.6f} exact={r} Sigma={[i for i in range(p) if A>>i&1]} |E|={e} Q_k={q}', 'FAIL' if r < 1 else 'ok')
