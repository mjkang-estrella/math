# Independent number-theory helpers (stdlib only), written from first principles.
import math

def vp(x, p):
    c = 0
    while x and x % p == 0:
        x //= p; c += 1
    return c

def factorint(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1 if p == 2 else 2
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

_ORD = {}
def order(g, p):
    """multiplicative order of g mod prime p"""
    key = (g % p, p)
    if key in _ORD: return _ORD[key]
    o = p - 1
    for q in factorint(p - 1):
        while o % q == 0 and pow(g, o // q, p) == 1:
            o //= q
    _ORD[key] = o
    return o

def lcm(a, b): return a * b // math.gcd(a, b)

# ---------- discrete logs ----------
def dlog_5k(h, k):
    """log base 3 of h in (Z/5^k)*, which is cyclic of order N=4*5^(k-1) with 3 a primitive root."""
    m = 5 ** k; N = 4 * 5 ** (k - 1)
    assert pow(3, N, m) == 1 and pow(3, N // 4, m) != 1 and (k == 1 or pow(3, N // 5, m) != 1)
    h %= m
    assert h % 5 != 0
    # CRT of: e mod 4 and e mod 5^(k-1)
    # mod 4:
    e4 = None
    t = pow(h, N // 4, m); g4 = pow(3, N // 4, m)
    for e in range(4):
        if pow(g4, e, m) == t: e4 = e; break
    assert e4 is not None
    # mod 5^(k-1), digit by digit
    e5 = 0
    if k >= 2:
        g5 = pow(3, N // 5, m)  # element of order 5
        for i in range(k - 1):
            # (h * 3^{-e5})^(N / 5^(i+1)) = g5^{d_i}
            cur = h * pow(3, -e5, m) % m
            t = pow(cur, N // 5 ** (i + 1), m)
            d = None
            for dd in range(5):
                if pow(g5, dd, m) == t: d = dd; break
            assert d is not None
            e5 += d * 5 ** i
    # combine
    N5 = 5 ** (k - 1)
    for e in range(e5, N, N5):
        if e % 4 == e4: break
    else: raise AssertionError
    assert pow(3, e, m) == h
    return e, N

def dlog_2k(x, m):
    """(sign s in {0,1}, u mod 2^(m-2)) with x = (-1)^s * 5^u mod 2^m, m>=3, x odd."""
    M = 2 ** m
    x %= M; assert x % 2 == 1
    s = 0 if x % 4 == 1 else 1
    y = x if s == 0 else (-x) % M
    u = 0
    for i in range(m - 2):
        mod = 2 ** (i + 3)
        if pow(5, u, mod) != y % mod: u |= 1 << i
    assert pow(5, u, M) == y
    return s, u

# ---------- integer lattice membership ----------
def lattice_member(cols, b):
    """Is b in the Z-span of the integer column vectors cols?  (rows = equations)"""
    r = len(b)
    cols = [list(c) for c in cols]
    active = list(range(len(cols)))
    pivots = []   # (row, col vector)
    for i in range(r):
        while True:
            nz = [c for c in active if cols[c][i] != 0]
            if len(nz) <= 1: break
            piv = min(nz, key=lambda c: abs(cols[c][i]))
            for c in nz:
                if c == piv: continue
                f = cols[c][i] // cols[piv][i]
                cols[c] = [x - f * y for x, y in zip(cols[c], cols[piv])]
        nz = [c for c in active if cols[c][i] != 0]
        if nz:
            pivots.append((i, cols[nz[0]])); active.remove(nz[0])
    res = list(b)
    pi = {i: c for i, c in pivots}
    for i in range(r):
        if i in pi:
            c = pi[i]
            if res[i] % c[i] != 0: return False
            f = res[i] // c[i]
            res = [x - f * y for x, y in zip(res, c)]
        else:
            if res[i] != 0: return False
    return True

def pin_unsolvable(K, t0, k, arange, wrange):
    """True iff NO (a,w) with a in arange, w in wrange satisfies 2^t0 * 3^a * 7^w == K (mod 10^k).
    ranges: (lo, hi) with hi == None meaning unbounded above, hi == lo exact.  Requires 2^t0 || K (K = 2^t0 * odd)."""
    assert K % (2 ** t0) == 0 and (K >> t0) % 2 == 1
    Kp = K >> t0
    mm = k - t0   # exponent of 2 for 3^a 7^w == Kp mod 2^mm
    rows_mod = []   # (vec3, vec7, vecK, modulus)
    # 5-part
    m5 = 5 ** k
    l7, N5 = dlog_5k(7, k)
    lK, _ = dlog_5k(K * pow(2, -t0, m5) % m5, k)
    rows_mod.append((1, l7, lK, N5))
    # 2-part
    if mm >= 3:
        s3, u3 = dlog_2k(3, mm); s7, u7 = dlog_2k(7, mm); sK, uK = dlog_2k(Kp, mm)
        rows_mod.append((s3, s7, sK, 2))
        rows_mod.append((u3, u7, uK, 2 ** (mm - 2)))
    elif mm == 2:
        rows_mod.append((1, 1, 0 if Kp % 4 == 1 else 1, 2))   # 3,7 = -1 mod 4
    # mm <= 1: no 2-adic condition
    b = [r[2] for r in rows_mod]
    cols = []
    (alo, ahi), (wlo, whi) = arange, wrange
    # shift by lower bounds
    b = [b[i] - alo * rows_mod[i][0] - wlo * rows_mod[i][1] for i in range(len(rows_mod))]
    if ahi is None: cols.append([r[0] for r in rows_mod])
    else: assert ahi == alo
    if whi is None: cols.append([r[1] for r in rows_mod])
    else: assert whi == wlo
    R = len(rows_mod)
    for i in range(R):
        v = [0] * R; v[i] = rows_mod[i][3]; cols.append(v)
    return not lattice_member(cols, b)

def pin_unsolvable_bruteforce(K, t0, k, arange, wrange):
    """independent check by direct enumeration of residues (only for small k)"""
    mod = 10 ** k
    (alo, ahi), (wlo, whi) = arange, wrange
    # periods of 3 and 7 mod 10^k
    def per(g):
        x = g % mod; n = 1
        while x != 1:
            x = x * g % mod; n += 1
            if n > 10 ** 6: raise ValueError
        return n
    p3, p7 = per(3), per(7)
    arng = [alo] if ahi is not None else range(alo, alo + p3)
    wrng = [wlo] if whi is not None else range(wlo, wlo + p7)
    t = pow(2, t0)
    for a in arng:
        x = t * pow(3, a, mod) % mod
        for w in wrng:
            if x * pow(7, w, mod) % mod == K % mod: return False
    return True
