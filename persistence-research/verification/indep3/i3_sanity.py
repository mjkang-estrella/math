import random, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i3_enum import *
random.seed(7)
# (1) equation 9n = 10^L + K + sum A_i 10^q_i  and  n mod 1000 = 111 + S_low  on random digit strings
for _ in range(30000):
    L = random.randint(3, 40); D = [random.choice((1, 1, 1, 2, 3, 4, 5, 6, 7, 8, 9)) for _ in range(L)]
    n = sum(d * 10 ** p for p, d in enumerate(D))
    S = sum((d - 1) * 10 ** p for p, d in enumerate(D[:3])); K = 9 * S - 1
    rhs = 10 ** L + K + sum(9 * (d - 1) * 10 ** p for p, d in enumerate(D) if p >= 3)
    assert 9 * n == rhs and n % 1000 == 111 + S
# (2) residue sets by direct enumeration of exponents
def direct(gens, mod, E=70):
    import itertools
    s = set()
    for ex in itertools.product(range(E), repeat=len(gens)):
        x = 1
        for g, e in zip(gens, ex): x = x * pow(g, e, mod) % mod
        s.add(x)
    return s
assert direct((2, 3, 7), 40) == R40 and direct((3, 7), 40) == R40o and direct((3, 7), 1000, 110) == R1000o and direct((3, 7), 200, 110) == R200o
assert direct((2, 3, 7), 1000, 40) == R1000
print('sanity ok; |R40|=%d |R40o|=%d |R1000|=%d |R1000o|=%d |R200o|=%d' % (len(R40), len(R40o), len(R1000), len(R1000o), len(R200o)))
# (3) every dead-config residue test, restated directly: dead config => no 7-smooth m<=10^7... skipped (lattice brute force replay covers this)
