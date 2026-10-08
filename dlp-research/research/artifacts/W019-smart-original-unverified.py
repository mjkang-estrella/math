#!/usr/bin/env python3
"""Synthetic checks. Toy fields only. No cryptographic keys."""
import time
T0 = time.perf_counter()
OPS = {"point_add": 0}

def egcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y

def inv(a, m):
    a %= m
    g, x, _ = egcd(a, m)
    if g != 1:
        raise ZeroDivisionError(g)
    return x % m

def tonelli(n, p):
    n %= p
    if n == 0:
        return 0
    if pow(n, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(n, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(n, q, p), pow(n, (q + 1) // 2, p)
    while t != 1:
        i, tt = 1, (t * t) % p
        while tt != 1:
            tt = (tt * tt) % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, (b * b) % p, (t * c) % p, (r * b) % p
    return r

def legendre(n, p):
    return pow(n % p, (p - 1) // 2, p)

def jac_dbl(P, a, M):
    X, Y, Z = P
    if Z % M == 0 or Y % M == 0:
        return (0, 1, 0)
    OPS["point_add"] += 1
    Y2 = (Y * Y) % M
    S = (4 * X * Y2) % M
    Z2 = (Z * Z) % M
    Z4 = (Z2 * Z2) % M
    M2 = (3 * X * X + a * Z4) % M
    X3 = (M2 * M2 - 2 * S) % M
    Y3 = (M2 * (S - X3) - 8 * Y2 * Y2) % M
    Z3 = (2 * Y * Z) % M
    return (X3, Y3, Z3)

def jac_add(P, Q, a, M):
    X1, Y1, Z1 = P
    X2, Y2, Z2 = Q
    if Z1 % M == 0:
        return Q
    if Z2 % M == 0:
        return P
    OPS["point_add"] += 1
    Z1Z1 = (Z1 * Z1) % M
    Z2Z2 = (Z2 * Z2) % M
    U1 = (X1 * Z2Z2) % M
    U2 = (X2 * Z1Z1) % M
    S1 = (Y1 * Z2 * Z2Z2) % M
    S2 = (Y2 * Z1 * Z1Z1) % M
    if U1 == U2:
        if (S1 - S2) % M == 0:
            return jac_dbl(P, a, M)
        return (0, 1, 0)
    H = (U2 - U1) % M
    R = (S2 - S1) % M
    HH = (H * H) % M
    HHH = (HH * H) % M
    U1HH = (U1 * HH) % M
    X3 = (R * R - HHH - 2 * U1HH) % M
    Y3 = (R * (U1HH - X3) - S1 * HHH) % M
    Z3 = (H * Z1 * Z2) % M
    return (X3, Y3, Z3)

def jac_mul(k, P, a, M):
    R = (0, 1, 0)
    Q = P
    kk = k
    while kk:
        if kk & 1:
            R = jac_add(R, Q, a, M)
        Q = jac_dbl(Q, a, M)
        kk >>= 1
    return R

def formal_t(P, p):
    """t = -x/y = -X*Z/Y for Jacobian (X:Y:Z), computed mod p^2.
    Strip a common factor of p so Y becomes a unit when the point is in E1.
    """
    M = p * p
    X, Y, Z = [c % M for c in P]
    removed = 0
    while removed < 2 and X % p == 0 and Y % p == 0 and Z % p == 0 and (X or Y or Z):
        X //= p
        Y //= p
        Z //= p
        removed += 1
    if Y % p == 0 or Z % p != 0:
        return None  # not a primitive E1 representative
    return (-X * Z * inv(Y, M)) % M

def hensel_y(x, y, a, b, p):
    M = p * p
    x %= p
    y0 = y % p
    f = (pow(x, 3, M) + (a % p) * x + (b % p)) % M
    delta = (f - pow(y0, 2, M)) % M
    assert delta % p == 0
    t = ((delta // p) * inv((2 * y0) % p, p)) % p
    Y = (y0 + t * p) % M
    assert (Y * Y - (pow(x, 3, M) + (a % p) * x + (b % p))) % M == 0
    return x, Y

def aff_add(P, Q, a, p):
    OPS["point_add"] += 1
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0:
        return None
    if P == Q:
        lam = ((3 * x1 * x1 + a) * inv(2 * y1, p)) % p
    else:
        lam = ((y2 - y1) * inv((x2 - x1) % p, p)) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)

def aff_mul(k, P, a, p):
    R = None
    Q = P
    while k:
        if k & 1:
            R = aff_add(R, Q, a, p)
        Q = aff_add(Q, Q, a, p)
        k >>= 1
    return R

def point_count(a, b, p):
    n = 1
    for x in range(p):
        rhs = (pow(x, 3, p) + a * x + b) % p
        leg = legendre(rhs, p)
        if leg == 0:
            n += 1
        elif leg == 1:
            n += 2
    return n

def all_affine(a, b, p):
    pts = []
    for x in range(p):
        rhs = (pow(x, 3, p) + a * x + b) % p
        for y in range(p):
            if (y * y) % p == rhs:
                pts.append((x, y))
    return pts

def smart_dlp(G, Q, a, b, p):
    M = p * p
    Gx, Gy = hensel_y(G[0], G[1], a, b, p)
    Qx, Qy = hensel_y(Q[0], Q[1], a, b, p)
    before = OPS["point_add"]
    JP = jac_mul(p, (Gx, Gy, 1), a, M)
    JQ = jac_mul(p, (Qx, Qy, 1), a, M)
    adds = OPS["point_add"] - before
    tP = formal_t(JP, p)
    tQ = formal_t(JQ, p)
    if tP is None or tQ is None or tP % p != 0 or (tP // p) % p == 0:
        return {"ok": False, "adds": adds, "tP": tP, "tQ": tQ, "JP": tuple(c % (p * p) for c in JP)}
    m = ((tQ // p) * inv((tP // p) % p, p)) % p
    return {"ok": True, "m": m, "adds": adds, "tP": tP, "tQ": tQ}

def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True

anoms = []
ords = []
for p in range(40, 120):
    if not is_prime(p):
        continue
    for a in range(0, 5):
        for b in range(1, 6):
            if (-16 * (4 * a * a * a + 27 * b * b)) % p == 0:
                continue
            N = point_count(a, b, p)
            if N == p and len(anoms) < 2:
                anoms.append((p, a, b))
            if N != p and is_prime(N) and N > 20 and len(ords) < 2:
                ords.append((p, a, b, N))
        if len(anoms) >= 2 and len(ords) >= 2:
            break
    if len(anoms) >= 2 and len(ords) >= 2:
        break

print("curves anomalous", anoms, "ordinary", ords)

for p, a, b in anoms:
    pts = [pt for pt in all_affine(a, b, p) if pt[1] % p != 0]
    G = pts[0]
    assert aff_mul(p, G, a, p) is None
    rows = []
    for m in (1, 2, 3, 7, 11, (p // 2)):
        m %= p
        if m == 0:
            continue
        Q = aff_mul(m, G, a, p)
        got = smart_dlp(G, Q, a, b, p)
        rows.append((m, got.get("m"), got["ok"] and got.get("m") == m, got["adds"]))
    print("ANOM", (p, a, b), "matches", sum(r[2] for r in rows), "/", len(rows), rows)

for p, a, b, N in ords:
    pts = [pt for pt in all_affine(a, b, p) if pt[1] % p != 0]
    G = pts[0]
    # generator may not have order N; take a point of order N by multiplying by cofactor 1 since N prime and N=#E so every non-O point generates if N prime.
    assert aff_mul(N, G, a, p) is None
    Q = aff_mul(3, G, a, p)
    pG = aff_mul(p % N, G, a, p)
    got = smart_dlp(G, Q, a, b, p)
    print("ORD", (p, a, b, N), "pG_is_O", pG is None, "procedure", got, "true", 3)

# Smart, HPL-97-128, worked example over F_43:
# Y^2 = X^3 - 4X^2 - 128X - 432, P=(0,16), Q=(12,1), claimed m=10.
# Depress X = u - A2/3 to short Weierstrass; the group isomorphism preserves the log.
p = 43
A2, A4, A6 = -4 % p, -128 % p, -432 % p
c = (A2 * inv(3, p)) % p  # X = u - c
assert (-3 * c + A2) % p == 0
a = (3 * c * c - 2 * A2 * c + A4) % p
b = (-pow(c, 3, p) + A2 * c * c - A4 * c + A6) % p
P = ((0 + c) % p, 16)
Q = ((12 + c) % p, 1)
assert (P[1] * P[1]) % p == (pow(P[0], 3, p) + a * P[0] + b) % p
assert (Q[1] * Q[1]) % p == (pow(Q[0], 3, p) + a * Q[0] + b) % p
got = smart_dlp(P, Q, a, b, p)
print("SMART_HPL97_EXAMPLE", {"N": point_count(a, b, p), "claimed_m": 10, "computed": got})

print("ops", OPS, "sec", round(time.perf_counter() - T0, 3))
