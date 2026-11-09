#!/usr/bin/env python3
"""Bounded scan: all n <= NMAX with >=3 distinct prime factors and gcd(2^n-1,n)=1.
Under the gcd condition every prime divisor of Phi_d(2) (d|n, d>1) is primitive (order exactly d),
so #distinct primes of 2^n-1 = sum_{d|n,d>1} omega(Phi_d(2)). A counterexample needs every
Phi_d(2) to be a prime power. We test: Phi_d(2) prime (BPSW-style strong PRP bases) -> 1; otherwise
check perfect power; if not a prime power, omega>=2 and n is not a counterexample.
Reports every n reaching exactly 2^ell - 1 under PRP (rigorous certification done separately)."""
import sys, math
NMAX = int(sys.argv[1]); ODD_ONLY = len(sys.argv) > 2
def mr(n, bases=(2,3,5,7,11,13,17,19,23,29,31,37,41)):
    if n < 2: return False
    for p in bases:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def primes_of(m):
    f = []; p = 2
    while p * p <= m:
        if m % p == 0:
            f.append(p)
            while m % p == 0: m //= p
        p += 1
    if m > 1: f.append(m)
    return f
def mobius(m):
    r = 1; p = 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
        p += 1
    return -r if m > 1 else r
cache = {}
def Phi2(d):
    if d not in cache:
        num = den = 1
        for e in range(1, d + 1):
            if d % e == 0:
                mu = mobius(d // e)
                if mu == 1: num *= 2**e - 1
                elif mu == -1: den *= 2**e - 1
        cache[d] = num // den
    return cache[d]
def is_perfect_power_prime(x):
    for k in range(2, x.bit_length() + 1):
        r = round(x ** (1.0 / k)) if x.bit_length() < 1000 else None
        if r is None: break
        for c in (r - 1, r, r + 1):
            if c > 1 and c**k == x and mr(c): return True
    return False
hits = []
for n in range(2, NMAX + 1):
    if ODD_ONLY and n % 2 == 0: continue
    ps = primes_of(n)
    if len(ps) < 3: continue
    if any(pow(2, n, p) == 1 for p in ps): continue
    ell = len(ps)
    divs = [d for d in range(2, n + 1) if n % d == 0]
    if len(divs) > 2**ell - 1: continue  # non-squarefree: tau(n)-1 >= 2^ell, conjecture holds trivially
    ok = True
    for d in sorted(divs):
        x = Phi2(d)
        if not (mr(x) or is_perfect_power_prime(x)): ok = False; break
    if ok: hits.append(n); print('COUNTEREXAMPLE-CANDIDATE', n, ps, flush=True)
print('scan complete NMAX=%d odd_only=%s hits=%s' % (NMAX, ODD_ONLY, hits))
