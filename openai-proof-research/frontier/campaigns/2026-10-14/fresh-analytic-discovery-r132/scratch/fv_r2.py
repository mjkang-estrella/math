# Exploration only (Monte Carlo with common random numbers): first variation off a triangle-group simplex point.
# T = standard triangle shifted by -p; ratio R = sum_{j<j'} psi(b_j-b_j') / ((n+1) Delta0 E phi(-sum b_j E_j)).
import math
import random
import sys


def make_samples(n, S, seed=12345):
    rng = random.Random(seed)
    return [[rng.expovariate(1.0) for _ in range(n)] for _ in range(S)]


def ratio(params, n, samples):
    p1, p2 = params[0], params[1]
    if p1 <= 1e-6 or p2 <= 1e-6 or p1 + p2 >= 1 - 1e-6:
        return 0.0
    q = 1 - p1 - p2
    verts = [(-p1, -p2), (1 - p1, -p2), (-p1, 1 - p2)]
    B = [(params[2 + 2 * j], params[3 + 2 * j]) for j in range(n)]
    num = 0.0
    for j in range(n):
        for jj in range(j + 1, n):
            vx, vy = B[j][0] - B[jj][0], B[j][1] - B[jj][1]
            num += sum(abs(vx * ay - vy * ax) for ax, ay in verts)
    acc = 0.0
    for e in samples:
        zx = -sum(B[j][0] * e[j] for j in range(n))
        zy = -sum(B[j][1] * e[j] for j in range(n))
        acc += max(-zx / p1, -zy / p2, (zx + zy) / q)
    den = (n + 1) * 1.0 * acc / len(samples)
    return num / den


def opt(n, seed, samples, rounds):
    rng = random.Random(seed)
    x = [rng.uniform(0.1, 0.4), rng.uniform(0.1, 0.4)] + [rng.gauss(0, 1) for _ in range(2 * n)]
    best = ratio(x, n, samples)
    step = 0.3
    for _ in range(rounds):
        y = [xi + step * rng.gauss(0, 1) * (0.3 if i < 2 else 1) for i, xi in enumerate(x)]
        v = ratio(y, n, samples)
        if v > best:
            best, x = v, y
        else:
            step = max(step * 0.997, 1e-4)
    return best, x


if __name__ == "__main__":
    n = int(sys.argv[1])
    S = int(sys.argv[2])
    seeds = int(sys.argv[3])
    rounds = int(sys.argv[4])
    samples = make_samples(n, S)
    for s in range(seeds):
        b, x = opt(n, s, samples, rounds)
        fresh = ratio(x, n, make_samples(n, 4 * S, seed=999 + s))
        print(n, s, round(b, 4), "fresh", round(fresh, 4), "p", [round(v, 3) for v in x[:2]], flush=True)
