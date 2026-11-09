#!/usr/bin/env python3
"""Bounded odd-case screen. An odd counterexample with ell=3 is n=pqr, p<q<r Mersenne-prime exponents,
with Phi_p(2),Phi_q(2),Phi_r(2) prime and Phi_{pq},Phi_{pr},Phi_{qr},Phi_{pqr}(2) all prime powers,
plus gcd(2^n-1,n)=1. Screen: list pairs p<q (odd Mersenne exponents, pq <= PQMAX) with Phi_pq(2) a
base-3 strong probable prime, then report triangles. Composite verdicts are rigorous (MR witness)."""
import sys, itertools
PQMAX = int(sys.argv[1])
MEXP = [3,5,7,13,17,19,31,61,89,107,127,521,607,1279,2203,2281,3217,4253,4423,9689,9941,11213]
def sprp(n, a=3):
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    x = pow(a, d, n)
    if x in (1, n - 1): return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1: return True
    return False
good = []
for p, q in itertools.combinations(MEXP, 2):
    if p * q > PQMAX: continue
    v = (2**(p*q) - 1) // ((2**p - 1) * (2**q - 1))
    # non-primitive factor possible only if p | 2^q-1 etc.; gcd condition then fails anyway for any n divisible by pq
    r = sprp(v)
    print(p, q, 'SPRP' if r else 'composite', flush=True)
    if r: good.append((p, q))
print('pairs with Phi_pq(2) SPRP:', good)
tri = [t for t in itertools.combinations(MEXP, 3) if all(pr in good for pr in itertools.combinations(t, 2))]
print('triangles:', tri)
