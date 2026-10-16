"""Numerical sanity check of the one-slice weighted interpolation bound.

Checks, for random convex L-Lipschitz u0, u1 on [a, b] and random positive
log-concave weights g <= Lam, that

    int |F'|^2 g  <=  18 h^-2 int F^2 g + 52 L^2 Lam h,   F = u0 - u1,

and also reports the ratio of the left side to the right side. This is
evidence only; the proof is in candidate.md.

Author: Myeongjin Kang. MIT License.
"""

import json
import math
import random
import sys


def convex_max_affine(rng, L, k):
    slopes = sorted(rng.uniform(-L, L) for _ in range(k))
    inters = [rng.uniform(-1.0, 1.0) for _ in range(k)]
    return lambda t: max(s * t + c for s, c in zip(slopes, inters)), \
        lambda t: max(zip(slopes, inters), key=lambda sc: sc[0] * t + sc[1])[0]


def log_concave_weight(rng, a, b):
    # log g = concave piecewise-linear minimum of affine pieces, plus a
    # concave quadratic; then normalized so that g integrates to one.
    k = rng.randint(1, 4)
    pieces = [(rng.uniform(-8, 8), rng.uniform(-2, 2)) for _ in range(k)]
    curv = rng.uniform(0, 20)
    centre = rng.uniform(a, b)
    return lambda t: min(p * t + q for p, q in pieces) - curv * (t - centre) ** 2


def one_trial(rng, n=4000):
    a, b = 0.0, rng.uniform(0.2, 3.0)
    L = rng.uniform(1.0, 3.0)
    u0, du0 = convex_max_affine(rng, L, rng.randint(2, 6))
    u1, du1 = convex_max_affine(rng, L, rng.randint(2, 6))
    lg = log_concave_weight(rng, a, b)
    dt = (b - a) / n
    ts = [a + (i + 0.5) * dt for i in range(n)]
    logs = [lg(t) for t in ts]
    m = max(logs)
    gs = [math.exp(v - m) for v in logs]
    z = sum(gs) * dt
    gs = [g / z for g in gs]
    lam = max(gs)
    F2 = sum((u0(t) - u1(t)) ** 2 * g for t, g in zip(ts, gs)) * dt
    G2 = sum((du0(t) - du1(t)) ** 2 * g for t, g in zip(ts, gs)) * dt
    best = None
    for h in [(b - a) * 2 ** (-j) for j in range(0, 12)]:
        rhs = 18.0 / h ** 2 * F2 + 52.0 * L ** 2 * lam * h
        r = G2 / rhs if rhs > 0 else 0.0
        if best is None or r > best[0]:
            best = (r, h)
    return best[0]


def main():
    rng = random.Random(20261016)
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    worst = 0.0
    for _ in range(trials):
        worst = max(worst, one_trial(rng))
    print(json.dumps({"check": "slice", "trials": trials,
                      "max_lhs_over_rhs": worst,
                      "passes": worst <= 1.0}))


if __name__ == "__main__":
    main()
