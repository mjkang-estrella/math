"""Structured family: lattice-convex sets S = conv(V) cap Z^k for random small V
in a box.  For such S every lattice line meets S in a contiguous run, so
n_S(d) = |S| - r_S(d) with r_S(d) = |S cap (S+d)| for primitive d.
Line-all-even  <=>  |S| even and r_S(d) even for every primitive d.
A spanning example in any Z^k (k>=3) would project generically to a
counterexample in R^3.  Exploration/support only.
Usage: latconv.py k side samples seed
"""
import sys, random, itertools, json
from math import gcd
import numpy as np
from scipy.spatial import ConvexHull

k, side, samples, seed = map(int, sys.argv[1:5])
rng = random.Random(seed)
box = np.array(list(itertools.product(range(side), repeat=k)))


def prim(v):
    g = 0
    for x in v:
        g = gcd(g, abs(int(x)))
    return g == 1


def lattice_hull(V):
    V = np.array(V, dtype=float)
    try:
        h = ConvexHull(V)
    except Exception:
        return None
    A, b = h.equations[:, :-1], h.equations[:, -1]
    ok = np.all(box @ A.T + b <= 1e-9, axis=1)
    return box[ok]


def odd_count(S):
    Sset = {tuple(p) for p in S}
    n = len(S)
    if n % 2:
        return None
    diffs = {}
    for p in S:
        for q in S:
            d = tuple(int(x) for x in q - p)
            if any(d) and prim(d):
                diffs[d] = diffs.get(d, 0) + 1
    # r(d) counted over ordered pairs with q-p=d exactly; unordered direction class {d,-d}
    odd = sum(1 for d, c in diffs.items() if c % 2 and d > tuple(-x for x in d))
    return odd


best = None
hist = {}
seen = set()
for t in range(samples):
    m = rng.randint(k + 1, k + 5)
    V = [tuple(rng.randrange(side) for _ in range(k)) for _ in range(m)]
    S = lattice_hull(V)
    if S is None:
        continue
    key = tuple(sorted(map(tuple, S)))
    if key in seen:
        continue
    seen.add(key)
    oc = odd_count(S)
    if oc is None:
        continue
    hist[oc] = hist.get(oc, 0) + 1
    if best is None or oc < best[0]:
        best = (oc, [list(map(int, p)) for p in S])
print(json.dumps({'k': k, 'side': side, 'distinct_even_size_sets': sum(hist.values()),
                  'odd_direction_histogram_low': {str(a): hist[a] for a in sorted(hist)[:6]},
                  'best': best}))
