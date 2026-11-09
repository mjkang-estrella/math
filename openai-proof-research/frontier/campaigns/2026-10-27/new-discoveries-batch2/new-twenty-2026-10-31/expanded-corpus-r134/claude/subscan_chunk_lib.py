import itertools
d = 3
F = list(range(1, 1 << d))
def apply(M, f):
    r = 0
    for b in range(d):
        if f >> b & 1: r ^= M[b]
    return r
perms = []
for M in itertools.product(F, repeat=d):
    imgs = [apply(M, f) for f in F]
    if len(set(imgs)) == len(F): perms.append([F.index(x) for x in imgs])
assert len(perms) == 168
def canon(m):
    best = None
    for p in perms:
        v = [0] * 7
        for a, b in enumerate(p): v[b] = m[a]
        t = tuple(v)
        if best is None or t > best: best = t
    return best
