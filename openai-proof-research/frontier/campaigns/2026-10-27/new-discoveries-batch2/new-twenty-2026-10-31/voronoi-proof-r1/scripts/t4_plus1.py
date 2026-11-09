# For every GL(3,2)-orbit of multiplicity vectors m with sum n in [lo,hi], decide equilibrium of m and of
# m + (1,...,1) (exact all-v convolution checker).  Tests the induction pattern "m EQ => m+1 EQ".
import sys; sys.path.insert(0, 'scripts')
from vk import *
import itertools, time, json
lo, hi = int(sys.argv[1]), int(sys.argv[2])
# GL(3,2) acting on functionals f (row vectors): f -> f o g for invertible g; implement via images of basis.
def apply(g, f):  # g: tuple of images of basis functionals e1,e2,e4 (as 3-bit masks)
    r = 0
    for i in range(3):
        if (f >> i) & 1: r ^= g[i]
    return r
GL = [g for g in itertools.product(range(1, 8), repeat=3) if len({apply(g, f) for f in range(1, 8)}) == 7]
assert len(GL) == 168
def canon(m):
    best = None
    for g in GL:
        mm = [0] * 7
        for f in range(1, 8): mm[apply(g, f) - 1] = m[f - 1]
        t = tuple(mm)
        if best is None or t > best: best = t
    return best
cache = {}
def eq(m):
    m = canon(m)
    if m not in cache:
        n = sum(m); P = positions(m)
        S = scores_all(n, P[1:])
        cache[m] = bool(S.max() * 8 <= (L << n))
    return cache[m]
t0 = time.time(); out = []
for n in range(lo, hi + 1):
    reps = sorted({canon(m) for m in itertools.product(range(n + 1), repeat=7) if sum(m) == n and len({f for f in range(1, 8) if m[f-1]}) and True}) if n <= 6 else None
    if reps is None:
        reps = set()
        for m in itertools.product(range(n + 1), repeat=6):
            s = sum(m)
            if s <= n: reps.add(canon(m + (n - s,)))
        reps = sorted(reps)
    # keep only profiles whose 8 points are distinct (functionals with m_f>0 span the dual)
    def spans(m):
        fs = [f for f in range(1, 8) if m[f - 1]]
        span = {0}
        for f in fs: span |= {s ^ f for s in span}
        return len(span) == 8
    reps = [m for m in reps if spans(m)]
    a = b = ab = 0; viol = []
    for m in reps:
        e1 = eq(m); e2 = eq(tuple(x + 1 for x in m))
        a += e1; b += e2; ab += e1 and e2
        if e1 and not e2: viol.append(m)
    print('n', n, 'orbits(distinct points)', len(reps), 'EQ', a, 'EQ after +1', b, 'both', ab, 'EQ but +1 not EQ:', viol[:12], len(viol), 'time', round(time.time()-t0,1), flush=True)
