#!/usr/bin/env python3
"""Exact finite controls for reduction-and-routes.md (F1, F3, Gauss, Theorem R
form 3 => 2 on a window, A3, O2, O3). Controls only: none of these checks is a
proof, and none bears on the open statement (N_Z)."""
import math
import sys
from itertools import product

failures = []


def check(name, ok):
    print(("ok   " if ok else "FAIL ") + name)
    if not ok:
        failures.append(name)


def g(t):
    return t * (2 * t + 1)


def tri(k):
    return k * (k + 1) // 2


def is_tri(n):
    if n < 0:
        return False
    r = math.isqrt(8 * n + 1)
    return r * r == 8 * n + 1


# F1: g is a bijection Z -> Tri.
B = 2000
vals = [g(t) for t in range(-B, B + 1)]
check("F1 injective on |t|<=2000", len(set(vals)) == len(vals))
check("F1 values triangular", all(is_tri(v) for v in vals))
check("F1 hits T(k) for k<=2*B-1", {tri(k) for k in range(2 * B)} <= set(vals))

# F3: w -> (w(w+1)/2, w(w-1)/2) is a bijection Z -> {(A,B) in N^2 : 2A=(A-B)(A-B+1)}.
ok = True
for w in range(-B, B + 1):
    A, Bv = w * (w + 1) // 2, w * (w - 1) // 2
    ok &= A >= 0 and Bv >= 0 and 2 * A == (A - Bv) * (A - Bv + 1) and A - Bv == w
check("F3 forward on |w|<=2000", ok)
sols = {(A, Bv) for A in range(301) for Bv in range(301) if 2 * A == (A - Bv) * (A - Bv + 1)}
image = {(w * (w + 1) // 2, w * (w - 1) // 2) for w in range(-30, 31)}
check("F3 inverse on [0,300]^2", sols == {p for p in image if max(p) <= 300})

# Gauss: every n <= 5000 is a sum of three triangular numbers.
T = [tri(k) for k in range(200) if tri(k) <= 5000]
Ts = set(T)
check("Gauss n<=5000", all(any((n - a - b) in Ts for a in T if a <= n for b in T if a + b <= n)
                          for n in range(5001)))


# Theorem R (3 => 2) on a window: integer t in Z^3 with sum g(t_i) = z and
# g(t) the lexicographically greatest Tri^3 representation of z; count must be [z >= 0].
def lexmax_rep(z):
    best = None
    for a in T:
        for b in T:
            c = z - a - b
            if c >= 0 and c in Ts:
                cand = (a, b, c)
                if best is None or cand > best:
                    best = cand
    return best


ok = True
for z in range(-60, 401):
    R = math.isqrt(abs(z)) + 2
    cnt = 0
    for t in product(range(-R, R + 1), repeat=3):
        tau = tuple(g(x) for x in t)
        if sum(tau) == z and tau == lexmax_rep(z):
            cnt += 1
    ok &= cnt == (1 if z >= 0 else 0)
check("Theorem R form-3 composite count on -60<=z<=400", ok)

# A3: #{s in Z : s^2 <= z < (s+1)^2} = [z >= 0].
ok = True
for z in range(-3000, 30001):
    R = math.isqrt(abs(z)) + 2
    cnt = sum(1 for s in range(-R, R + 1) if s * s <= z < (s + 1) * (s + 1))
    ok &= cnt == (1 if z >= 0 else 0)
check("A3 singleton/empty on -3000<=z<=30000", ok)


# O2: residues of +-eps^n mod M are periodic in n, so every residue class
# reached by a Pell solution is reached by many distinct solutions.
def pell_fund(D):
    w = 1
    while True:
        y2 = 1 + D * w * w
        y = math.isqrt(y2)
        if y * y == y2:
            return y, w
        w += 1


ok = True
for D in (2, 3, 5, 6, 7, 10, 11):
    y1, w1 = pell_fund(D)
    sols = []
    y, w = 1, 0
    for n in range(0, 121):
        for s in (1, -1):
            sols.append((s * y, s * w))
            sols.append((s * y, -s * w))  # eps^{-n}
        y, w = y * y1 + D * w * w1, y * w1 + w * y1
    sols = set(sols)
    ok &= all(yy * yy - D * ww * ww == 1 for yy, ww in sols)
    for M in range(2, 13):
        counts = {}
        for yy, ww in sols:
            key = (yy % M, ww % M)
            counts[key] = counts.get(key, 0) + 1
        ok &= min(counts.values()) >= 2
check("O2 Pell residue classes repeat (D<=11, M<=12, |n|<=120)", ok)

# O3 arithmetic: g(e) >= e^2 for all e, and W >= 2^(W/4) fails exactly for W >= 17.
check("O3 g(e)>=e^2 on |e|<=10^4", all(g(e) >= e * e for e in range(-10**4, 10**4 + 1)))
check("O3 W>=2^(W/4) fails for 17<=W<=400 and holds at W=16",
      all(W ** 4 < 2 ** W for W in range(17, 401)) and 16 ** 4 >= 2 ** 16)

print("controls:", "all passed" if not failures else f"{len(failures)} failed")
sys.exit(1 if failures else 0)
