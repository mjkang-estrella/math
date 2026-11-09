# highdim number theory helpers (generator side only; the checkers use their own code).
import math, random

def vp(x, p):
    c = 0
    while x and x % p == 0:
        x //= p; c += 1
    return c

_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
def is_prime(n):
    """deterministic Miller-Rabin for n < 3.3e24"""
    if n < 2: return False
    for p in _MR_BASES:
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

def rho(n, budget=200000):
    if n % 2 == 0: return 2
    for c in range(1, 20):
        y, r, q, g = random.randrange(n), 1, 1, 1
        x = ys = y; it = 0
        f = lambda v: (v * v + c) % n
        while g == 1:
            x = y
            for _ in range(r): y = f(y)
            k = 0
            while k < r and g == 1:
                ys = y
                for _ in range(min(128, r - k)):
                    y = f(y); q = q * abs(x - y) % n
                g = math.gcd(q, n); k += 128; it += 128
                if it > budget: return None
            r *= 2
        if g == n:
            g = 1
            while g == 1:
                ys = f(ys); g = math.gcd(abs(x - ys), n)
        if g != n: return g
    return None

def factor_partial(n, budget=200000, small=10 ** 5):
    """returns (list of prime factors found with multiplicity, unfactored cofactor)"""
    out = []
    for p in range(2, small):
        if p * p > n: break
        while n % p == 0: out.append(p); n //= p
    stack, rest = [n] if n > 1 else [], 1
    while stack:
        m = stack.pop()
        if m == 1: continue
        if is_prime(m): out.append(m); continue
        g = rho(m, budget)
        if g is None: rest *= m; continue
        stack += [g, m // g]
    return sorted(out), rest

def factorint(n):
    f, r = factor_partial(n, budget=10 ** 7)
    assert r == 1, n
    d = {}
    for p in f: d[p] = d.get(p, 0) + 1
    return d

def order(g, p, fac=None):
    if fac is None: fac = factorint(p - 1)
    o = p - 1
    for q in fac:
        while o % q == 0 and pow(g, o // q, p) == 1: o //= q
    return o

def cyclotomic_value(d, x=10):
    """Phi_d(x) via Moebius product"""
    num, den = 1, 1
    for e in divisors(d):
        mu = mobius(d // e)
        if mu == 1: num *= x ** e - 1
        elif mu == -1: den *= x ** e - 1
    assert num % den == 0
    return num // den

def mobius(n):
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0: return 0
            r = -r
        p += 1
    return -r if n > 1 else r

def divisors(n):
    ds = [1]
    for p, e in factorint(n).items():
        ds = [x * p ** k for x in ds for k in range(e + 1)]
    return sorted(ds)

def lcm(a, b): return a * b // math.gcd(a, b)
