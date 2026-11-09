# Soundness test of Region.kill_prime: build equations with known solutions and verify the class of the solution is never killed.
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from region import Region
from nt import vp, isprime
random.seed(12345)
primes = [p for p in range(11, 4000) if isprime(p)]
tested = killed_other = 0
for trial in range(3000):
    dim = random.choice([2, 3])
    coefs = [9, 9] if dim == 3 else [random.choice([9, 18, 27])]
    if dim == 3:
        q1 = random.randint(3, 6); q2 = random.randint(q1 + 1, 9); L = random.randint(q2 + 1, 12); x = (L, q1, q2)
    else:
        q = random.randint(3, 8); L = random.randint(q + 1, 12); x = (L, q)
    t = random.randint(0, min(x[1:]) - 1)
    a = random.randint(0, 25); w = random.randint(0, 14)
    N = 2 ** t * 3 ** a * 7 ** w
    base = 10 ** L + sum(c * 10 ** e for c, e in zip(coefs, x[1:]))
    K = N - base
    if K <= 0 or K % 5 == 0 or K > 10 ** 12: continue
    if vp(K, 2) != t: continue
    R = Region(coefs, K)
    for _ in range(8):
        M = random.choice([1, 2, 3, 6, 12, 18, 42, 36, 126, 252, 30, 84])
        p = random.choice(primes)
        r = tuple(v % M for v in x)
        tested += 1
        assert not R.kill_prime(p, r, M), ("UNSOUND", coefs, K, x, a, w, M, p)
        # also a coarser family with the exact lift
print("soundness test passed on", tested, "(solution-class, prime) pairs")
# kill-power sanity: classes NOT containing a solution should often be killed
