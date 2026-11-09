"""Minimal exact-integer number theory helpers (no external deps)."""
import random
from math import gcd
def _mr(n, a):
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    x = pow(a, d, n)
    if x in (1, n-1): return True
    for _ in range(s-1):
        x = x*x % n
        if x == n-1: return True
    return False
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if not _mr(n,a): return False
    return True
def _pollard(n):
    if n % 2 == 0: return 2
    while True:
        x = random.randrange(2, n); y = x; c = random.randrange(1, n); d = 1
        while d == 1:
            x = (x*x+c) % n; y = (y*y+c) % n; y = (y*y+c) % n
            d = gcd(abs(x-y), n)
        if d != n: return d
def factorint(n):
    fs = {}
    stack = [n]
    while stack:
        m = stack.pop()
        if m == 1: continue
        if is_prime(m): fs[m] = fs.get(m,0)+1; continue
        d = _pollard(m)
        stack += [d, m//d]
    return dict(sorted(fs.items()))
def divisors(n):
    fs = factorint(n)
    ds = [1]
    for p,e in fs.items():
        ds = [d*p**k for d in ds for k in range(e+1)]
    return sorted(ds)
def n_order(a, n):
    # multiplicative order of a mod n (n>=1, gcd(a,n)=1)
    if n == 1: return 1
    t = 1; x = a % n
    while x != 1:
        x = x*a % n; t += 1
        if t > 10**8: raise RuntimeError("order too large")
    return t
def order_fast(a, n, group_order):
    # order divides group_order: factor it
    o = group_order
    for p,e in factorint(group_order).items():
        while o % p == 0 and pow(a, o//p, n) == 1:
            o //= p
    return o
def invmod(a, n):
    """Modular inverse of a mod n (n > 1, gcd(a,n)=1)."""
    return pow(a, -1, n)

def v_p(n, p):
    if n == 0: return 10**9
    v = 0
    while n % p == 0: n //= p; v += 1
    return v
