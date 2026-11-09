"""Closed-form mean subtree order of K_{a,b} and of K_{a,b}+e (e inside side X of size a), exact integers.
Subtree vertex set with p vertices in X and q in Y: tau = p^(q-1) q^(p-1) if p,q>=1; singletons tau=1.
Usage: msto_kab.py amin amax bmax   (prints sign of delta for edge inside small side X (size a) and inside side Y (size b))
"""
import sys
from math import comb
from fractions import Fraction

def tau(p, q):
    if p == 0 and q == 0: return 0
    if p == 0: return 1 if q == 1 else 0
    if q == 0: return 1 if p == 1 else 0
    return p ** (q - 1) * q ** (p - 1)

def NR(a, b):
    N = R = 0
    for p in range(a + 1):
        for q in range(b + 1):
            t = tau(p, q)
            if t:
                c = comb(a, p) * comb(b, q) * t
                N += c; R += c * (p + q)
    return N, R

def pair(a, b):
    """u,v both in X (size a). sum over disjoint S∋u (not v), S'∋v (not u)."""
    A = B = 0
    # S: p1 in X (incl u), q1 in Y ; S': p2 in X (incl v), q2 in Y
    for p1 in range(1, a):
        for q1 in range(0, b + 1):
            t1 = tau(p1, q1)
            if not t1: continue
            c1 = comb(a - 2, p1 - 1) * comb(b, q1)
            for p2 in range(1, a - p1 + 1):
                if (p1 - 1) + (p2 - 1) > a - 2: continue
                c2x = comb(a - 2 - (p1 - 1), p2 - 1)
                for q2 in range(0, b - q1 + 1):
                    t2 = tau(p2, q2)
                    if not t2: continue
                    w = c1 * c2x * comb(b - q1, q2) * t1 * t2
                    A += w; B += w * (p1 + q1 + p2 + q2)
    return A, B

def delta(a, b, side):
    N, R = NR(a, b)
    A, B = pair(a, b) if side == 'X' else pair(b, a)
    return Fraction(R + B, N + A) - Fraction(R, N)

if __name__ == '__main__':
    amin, amax, bmax = map(int, sys.argv[1:4])
    for a in range(amin, amax + 1):
        row = []
        for b in range(max(a, 2), bmax + 1):
            dX = delta(a, b, 'X') if a >= 2 else None
            dY = delta(a, b, 'Y')
            row.append((b, None if dX is None else float(dX), float(dY)))
            flag = ' BOTH<=0 !!!' if (dX is None or dX <= 0) and dY <= 0 else ''
            print(f'K{a},{b}: dX={float(dX) if dX is not None else None:+.3e} dY={float(dY):+.3e}{flag}', flush=True)
