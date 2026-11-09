"""371607 diagnostic: binary automata on Q = {0..n-1}, letters a, b.
mode 'perm': a runs over one representative permutation per cycle type, b over all maps.
mode 'all': a, b over all maps (small n only).
Reports synchronizing, rank-2-free, C-irreducible examples (Burnside dimension test mod two primes).
usage: automata_binary.py n mode [maxprint]
"""
import sys, itertools
sys.path.insert(0, sys.argv[0].rsplit('/', 1)[0])
n = int(sys.argv[1]); mode = sys.argv[2]; maxprint = int(sys.argv[3]) if len(sys.argv) > 3 else 10
PR = [1000000007, 998244353]

def images(maps):
    start = frozenset(range(n)); seen = {start}; st = [start]
    while st:
        S = st.pop()
        for m in maps:
            T = frozenset(m[x] for x in S)
            if T not in seen:
                seen.add(T); st.append(T)
    return seen

def mat(m):
    M = [0] * ((n - 1) * (n - 1))
    for i in range(1, n):
        for s, sg in ((m[i], 1), (m[0], -1)):
            if s != 0:
                M[(i - 1) * (n - 1) + s - 1] += sg
    return M

def monoid(maps):
    idm = tuple(range(n)); seen = {idm}; st = [idm]
    while st:
        u = st.pop()
        for m in maps:
            w = tuple(m[u[x]] for x in range(n))
            if w not in seen:
                seen.add(w); st.append(w)
    return seen

def rank_mod(vecs, p):
    rows = {}
    for v in vecs:
        v = [x % p for x in v]
        for c, r in rows.items():
            if v[c]:
                t = v[c]; v = [(x - t * y) % p for x, y in zip(v, r)]
        nz = next((i for i, x in enumerate(v) if x), None)
        if nz is not None:
            inv = pow(v[nz], p - 2, p); rows[nz] = [x * inv % p for x in v]
    return len(rows)

def irreducible(maps):
    vecs = [mat(u) for u in monoid(maps)]
    return all(rank_mod(vecs, p) == (n - 1) ** 2 for p in PR)

def partitions(m, mx=None):
    if mx is None: mx = m
    if m == 0:
        yield []; return
    for k in range(min(m, mx), 0, -1):
        for r in partitions(m - k, k):
            yield [k] + r

def perm_of(ct):
    p = [0] * n; s = 0
    for c in ct:
        for j in range(c):
            p[s + j] = s + (j + 1) % c
        s += c
    return tuple(p)

if mode == 'perm':
    As = [perm_of(ct) for ct in partitions(n)]
else:
    As = list(itertools.product(range(n), repeat=n))
found = cand = checked = 0
for A in As:
    for B in itertools.product(range(n), repeat=n):
        if mode == 'all' and B < A:
            continue
        checked += 1
        sizes = {len(S) for S in images([A, B])}
        if 1 not in sizes or 2 in sizes:
            continue
        cand += 1
        if irreducible([A, B]):
            found += 1
            if found <= maxprint:
                print('FOUND n=%d a=%s b=%s sizes=%s' % (n, A, B, sorted(sizes)))
print('n=%d mode=%s checked=%d sync_no_rank2=%d irreducible=%d' % (n, mode, checked, cand, found))
