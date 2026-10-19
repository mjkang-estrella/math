"""Finite sanity checks for the weighted-rank (conditional Bernoulli) comparisons.

These exact rational computations only probe the feasibility claims recorded in
packet/public/weighted-rank-feasibility.md; they are not proofs or gates.
"""
from fractions import Fraction as Fr
from itertools import combinations
import random, math


def esym(ws, k):
    e = [Fr(1)] + [Fr(0)] * k
    for w in ws:
        for j in range(k, 0, -1):
            e[j] += e[j - 1] * w
    return e


def containment(w, k, S):
    rest = [w[i] for i in range(len(w)) if i not in S]
    if len(S) > k:
        return Fr(0)
    num = Fr(1)
    for i in S:
        num *= w[i]
    return num * esym(rest, k - len(S))[k - len(S)] / esym(w, k)[k]


def mean_field(w, k):
    # t with sum t w/(1+t w) = k, by bisection in floats then rational p
    lo, hi = 1e-12, 1e12
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        s = sum(mid * x / (1 + mid * x) for x in w)
        if s < k:
            lo = mid
        else:
            hi = mid
    t = math.sqrt(lo * hi)
    return [t * x / (1 + t * x) for x in w]


def light_check(trials=300, seed=1):
    rng = random.Random(seed)
    worst_lower, worst_marg = float('inf'), 0.0
    for _ in range(trials):
        n = rng.randint(4, 10)
        k = rng.randint(1, n // 2)
        w = [Fr(rng.randint(1, 30)) for _ in range(n)]
        p = mean_field([float(x) for x in w], k)
        if max(p) > 0.5:
            continue
        for i in range(n):
            pi = float(containment(w, k, (i,)))
            worst_marg = max(worst_marg, pi / p[i])
        for s in range(1, k + 1):
            for S in combinations(range(n), s):
                c = float(containment(w, k, S))
                prod = math.prod(p[i] for i in S)
                worst_lower = min(worst_lower, (c / prod) ** (1 / s))
    return worst_lower, worst_marg


def overload_example(m, eps):
    # half the coordinates have mean-field p=0.55 (set A), half have p=1-eps
    wa = 0.55 / 0.45
    wb = (1 - eps) / eps
    w = [Fr(wa).limit_denominator(10**6)] * m + [Fr(wb).limit_denominator(10**9)] * m
    k = round(0.55 * m + (1 - eps) * m)
    p = mean_field([float(x) for x in w], k)
    S = tuple(range(m))
    c = float(containment(w, k, S))
    prod = math.prod(p[i] for i in S)
    return k, (c / prod) ** (1 / m)


def sandwich_example(M):
    # exact containment values for n=3, k=2, w=(M,1,1)
    w = [Fr(M), Fr(1), Fr(1)]
    single = containment(w, 2, (1,))
    pair = containment(w, 2, (1, 2))
    assert single == Fr(M + 1, 2 * M + 1) and pair == Fr(1, 2 * M + 1)
    # any product p with a^2 p2 p3 <= pair and single <= b p2, b p3 forces (b/a)^2 >= single^2/pair
    return single ** 2 / pair


if __name__ == '__main__':
    lo, marg = light_check()
    print('light regime sample: min (c/prod p)^(1/s) =', round(lo, 4), ' (reference constant 1/(2e)=', round(1 / (2 * math.e), 4), 'is not proved here)')
    print('light regime sample: max pi_i/p_i =', round(marg, 4))
    for M in [10, 100, 10**4]:
        print(f'sandwich example M={M}: forced (b/a)^2 >= {sandwich_example(M)}')
    for m, eps in [(20, 0.05), (20, 0.01), (40, 0.01), (40, 0.002)]:
        k, r = overload_example(m, eps)
        print(f'overload example m={m} eps={eps} k={k}: (c/prod p)^(1/s) = {r:.3e}')
