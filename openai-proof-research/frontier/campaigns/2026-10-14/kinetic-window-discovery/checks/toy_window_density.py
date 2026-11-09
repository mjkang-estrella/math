#!/usr/bin/env python3
"""Illustration (NOT proof) of Lemma A on the smallest cyclic history.

Three lines a,b,c born at 0, dynamic mergers (a,b) at s1 and (a,c) at s2,
0<s1<s2<tau=1, and a redundant a-b recontact at the determined time t*.
Chart weight (common eps^4 and activity factors dropped): standard Gaussian
birth velocities, uniform normals, flux [u1.w1]_+ [u2.w2]_+, ordered times.

Lemma A predicts, for every window W,
   mass{t* in W} <= (|W|/Lam) * (1+Lam)^2 * M_full,   Lam = tau/(1+a), a=2,
where M_full is the total chart mass WITHOUT the recollision requirement.
We estimate the left side by Monte Carlo on a grid of windows and report the
worst ratio to the right side.  Deterministic seed; standard library only.
"""
import math
import random
import sys

def dot(a, b): return sum(x * y for x, y in zip(a, b))
def sub(a, b): return [x - y for x, y in zip(a, b)]
def add(a, b): return [x + y for x, y in zip(a, b)]
def mul(c, a): return [c * x for x in a]

def unit(rng):
    while True:
        w = [rng.gauss(0, 1) for _ in range(3)]
        n = math.sqrt(dot(w, w))
        if n > 1e-12:
            return mul(1 / n, w)

def sample(rng, eps):
    va, vb, vc = ([rng.gauss(0, 1) for _ in range(3)] for _ in range(3))
    s1, s2 = sorted((rng.random(), rng.random()))
    w1, w2 = unit(rng), unit(rng)
    f1 = dot(sub(va, vb), w1)
    if f1 <= 0:
        return 0.0, None
    c1 = f1
    va1, vb1 = sub(va, mul(c1, w1)), add(vb, mul(c1, w1))
    f2 = dot(sub(va1, vc), w2)
    if f2 <= 0:
        return 0.0, None
    va2 = sub(va1, mul(f2, w2))
    weight = f1 * f2
    # relative position b - a at s2, then flight with u = vb1 - va2
    r = add(mul(eps, w1), mul(s2 - s1, sub(vb1, va1)))
    u = sub(vb1, va2)
    A, B, C = dot(u, u), 2 * dot(r, u), dot(r, r) - eps * eps
    disc = B * B - 4 * A * C
    if A < 1e-14 or disc <= 0:
        return weight, None
    t = (-B - math.sqrt(disc)) / (2 * A)
    if t <= 0:
        return weight, None
    return weight, s2 + t

def main():
    rng = random.Random(7)
    n_samp, eps, a = 400_000, 0.25, 2
    lam = 1 / (1 + a)
    tot, hits = 0.0, []
    for _ in range(n_samp):
        w, ts = sample(rng, eps)
        tot += w
        if ts is not None:
            hits.append((ts, w))
    m_full = tot / n_samp
    worst = 0.0
    for width in (0.4, 0.1, 0.02):
        k = 0.0
        while k + width <= 2.0:
            mass = sum(w for t, w in hits if k <= t < k + width) / n_samp
            bound = (width / lam) * (1 + lam) ** 2 * m_full
            worst = max(worst, mass / bound)
            k += width / 2
    frac = sum(w for _, w in hits) / tot
    print(f"eps={eps} samples={n_samp} recollision mass fraction={frac:.4f}")
    print(f"worst window ratio mass/LemmaA-bound = {worst:.4f} (must be <= 1)")
    print("PASS" if worst <= 1 else "FAIL")
    return 0 if worst <= 1 else 1

if __name__ == "__main__":
    sys.exit(main())
