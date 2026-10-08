#!/usr/bin/env python3
"""Audit probe 3: independent re-derivation of cheap report numbers whose scripts
are NOT on disk (only exp1_smart.py was preserved)."""
import time, math
T0 = time.perf_counter()

def inv(a, m): return pow(a, -1, m)
def pts(a, b, p):
    out = [None]
    for x in range(p):
        r = (x**3 + a*x + b) % p
        for y in range(p):
            if (y*y) % p == r: out.append((x, y))
    return out
def add(P, Q, a, p):
    if P is None: return Q
    if Q is None: return P
    if P[0] == Q[0] and (P[1] + Q[1]) % p == 0: return None
    lam = ((3*P[0]**2 + a) * inv(2*P[1], p)) % p if P == Q else ((Q[1]-P[1]) * inv((Q[0]-P[0]) % p, p)) % p
    x3 = (lam*lam - P[0] - Q[0]) % p
    return (x3, (lam*(P[0]-x3) - P[1]) % p)

# (a) Semaev f_3 identity on y^2=x^3+x+1 over F_17, all 17^3 x-triples
p, a, b = 17, 1, 1
def f3(x1, x2, x3):
    return ((x1-x2)**2 * x3**2 - 2*((x1+x2)*(x1*x2+a) + 2*b)*x3 + ((x1*x2-a)**2 - 4*b*(x1+x2))) % p
P = pts(a, b, p)
byx = {}
for Q in P[1:]: byx.setdefault(Q[0], []).append(Q)
zeros = mism = 0
for x1 in range(p):
    for x2 in range(p):
        for x3 in range(p):
            alg = f3(x1, x2, x3) == 0
            geo = False
            for P1 in byx.get(x1, []):
                for P2 in byx.get(x2, []):
                    S = add(P1, P2, a, p)
                    if S is not None and S[0] == x3: geo = True
            # points with x not on curve over F_p: Semaev's identity is over the closure, so
            # restrict the comparison to x-values that are F_p-rational x-coordinates
            if x1 in byx and x2 in byx and x3 in byx:
                zeros += alg; mism += (alg != geo)
print("(a) F_17 f_3 zeros among rational x-triples:", zeros, "mismatches:", mism,
      "(report: 136 zeros, 0 mismatches over 729 triples)")

# (b) orbit-index numbers for y^2=x^3+1, p=13 and p=109
for p in (13, 109):
    P = pts(0, 1, p)
    N = len(P)
    neg_classes = len({frozenset([Q, None if Q is None else (Q[0], (-Q[1]) % p)]) for Q in P})
    beta = next(z for z in range(2, p) if pow(z, 3, p) == 1 and z != 1)
    def orb(Q):
        if Q is None: return frozenset([None])
        s = set()
        for k in range(3):
            x = (pow(beta, k, p) * Q[0]) % p
            s.add((x, Q[1])); s.add((x, (-Q[1]) % p))
        return frozenset(s)
    six_classes = len({orb(Q) for Q in P})
    print("(b) p=%d N=%d N/neg=%.2f N/six=%.2f sqrt: %.2f %.2f" % (p, N, N/neg_classes, N/six_classes,
          math.sqrt(N/neg_classes), math.sqrt(N/six_classes)))

# (c) secp256k1 lambda eigenvalue check (public constants, no secret)
pp = 2**256 - 2**32 - 977
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
lam = 0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce
def jmul(k, X, Y):
    R = None
    Q = (X, Y)
    while k:
        if k & 1: R = add(R, Q, 0, pp)
        Q = add(Q, Q, 0, pp); k >>= 1
    return R
LG = jmul(lam, Gx, Gy)
beta = (LG[0] * inv(Gx, pp)) % pp
print("(c) lam^2+lam+1 == 0 mod n:", (lam*lam + lam + 1) % n == 0, "; [lam]G = (beta*Gx, Gy):", LG[1] == Gy,
      "; beta^3 == 1 mod p:", pow(beta, 3, pp) == 1, "; n != p:", n != pp)
print("(d) apparent-exponent: log(sqrt(N/6))/log N at N=108, 1e6, 2^128, 2^256:",
      [round(0.5*(math.log(N) - math.log(6))/math.log(N), 3) for N in (108, 1e6, 2.0**128, 2.0**256)])
print("sec", round(time.perf_counter() - T0, 3))
