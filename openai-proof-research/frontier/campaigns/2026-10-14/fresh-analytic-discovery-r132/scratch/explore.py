# Exploration only (floating point); not a proof. Phi_m(a) = D(a) * max_t M(t|a) / (m-1)^2,
# M = B-spline density with knots a (density of <a,s>, s uniform on the simplex Delta^{m-1}).
import random
import sys


def bspline_density(t, a):
    a = sorted(a)
    m = len(a)
    if not (a[0] < t < a[-1]):
        return 0.0
    N = [1.0 if a[i] <= t < a[i + 1] else 0.0 for i in range(m - 1)]
    for k in range(2, m):
        new = []
        for i in range(m - k):
            v = 0.0
            d1 = a[i + k - 1] - a[i]
            d2 = a[i + k] - a[i + 1]
            if d1 > 0:
                v += (t - a[i]) / d1 * N[i]
            if d2 > 0:
                v += (a[i + k] - t) / d2 * N[i + 1]
            new.append(v)
        N = new
    return (m - 1) / (a[-1] - a[0]) * N[0]


def maxM(a, iters=80):
    lo, hi = min(a), max(a)
    for _ in range(iters):
        x1 = lo + (hi - lo) * 0.381966
        x2 = lo + (hi - lo) * 0.618034
        if bspline_density(x1, a) < bspline_density(x2, a):
            lo = x1
        else:
            hi = x2
    t = (lo + hi) / 2
    return bspline_density(t, a), t


def D(a):
    s = sorted(a)
    m = len(s)
    return sum((2 * i - m + 1) * s[i] for i in range(m))


def Phi(a):
    mm, t = maxM(a)
    return D(a) * mm / (len(a) - 1) ** 2, t


def optimize(m, seed, rounds=3000):
    rng = random.Random(seed)
    x = sorted(rng.random() for _ in range(m - 2))
    best = Phi([0.0] + x + [1.0])[0]
    step = 0.2
    for r in range(rounds):
        y = [min(1.0, max(0.0, xi + step * rng.gauss(0, 1))) for xi in x]
        v = Phi([0.0] + y + [1.0])[0]
        if v > best:
            best, x = v, y
        else:
            step = max(step * 0.995, 1e-5)
    return best, sorted(x)


if __name__ == "__main__":
    m = int(sys.argv[1])
    seeds = int(sys.argv[2])
    out = []
    for s in range(seeds):
        b, x = optimize(m, s)
        out.append((b, x))
    out.sort(reverse=True)
    for b, x in out[:5]:
        print(m, round(b, 10), [round(v, 5) for v in x])
