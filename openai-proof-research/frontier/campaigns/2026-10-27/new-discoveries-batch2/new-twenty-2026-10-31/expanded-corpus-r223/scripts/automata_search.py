"""371607 diagnostic: binary circular automata Q = Z_n, a: i -> i+1, b: arbitrary map.
Report b such that: synchronizing, no word of rank 2, and the synchronized representation on
the sum-zero subspace is C-irreducible (Burnside: span of word matrices = full (n-1)^2 algebra).
Rank of span computed modulo two large primes (diagnostic); exact recheck separately.
usage: automata_search.py n [maxprint]
"""
import sys, itertools

n = int(sys.argv[1]); maxprint = int(sys.argv[2]) if len(sys.argv) > 2 else 20
a = tuple((i + 1) % n for i in range(n))
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

def mat(m):  # action on basis v_i = q_i - q_0 (i=1..n-1): v_i -> q_{m(i)} - q_{m(0)}
    M = [[0] * (n - 1) for _ in range(n - 1)]
    for i in range(1, n):
        for st, sg in ((m[i], 1), (m[0], -1)):
            if st != 0:
                M[i - 1][st - 1] += sg
    return M  # row i = image of v_i

def compose(m1, m2):  # first m1 then m2
    return tuple(m2[m1[x]] for x in range(n))

def monoid(maps):
    idm = tuple(range(n)); seen = {idm}; st = [idm]
    while st:
        u = st.pop()
        for m in maps:
            w = compose(u, m)
            if w not in seen:
                seen.add(w); st.append(w)
    return seen

def rank_mod(vecs, p):
    rows = []; piv = []
    for v in vecs:
        v = [x % p for x in v]
        for (c, r) in zip(piv, rows):
            if v[c]:
                t = v[c]
                v = [(x - t * y) % p for x, y in zip(v, r)]
        nz = next((i for i, x in enumerate(v) if x), None)
        if nz is not None:
            inv = pow(v[nz], p - 2, p)
            v = [x * inv % p for x in v]
            rows.append(v); piv.append(nz)
    return len(rows)

def irreducible(maps):
    vecs = [sum(mat(u), []) for u in monoid(maps)]
    return all(rank_mod(vecs, p) == (n - 1) ** 2 for p in PR)

def canon(b):  # conjugate by rotations r^k (commute with a)
    best = None
    for k in range(n):
        c = tuple((b[(x - k) % n] + k) % n for x in range(n))
        if best is None or c < best:
            best = c
    return best

found = 0; checked = 0; cand = 0
for b in itertools.product(range(n), repeat=n):
    if canon(b) != b:
        continue
    if len(set(b)) == n:
        continue
    checked += 1
    im = images([a, b])
    sizes = {len(S) for S in im}
    if 1 not in sizes or 2 in sizes:
        continue
    cand += 1
    if irreducible([a, b]):
        found += 1
        if found <= maxprint:
            print('FOUND n=%d b=%s rank(b)=%d sizes=%s' % (n, b, len(set(b)), sorted(sizes)))
print('n=%d checked=%d sync_no_rank2=%d irreducible=%d' % (n, checked, cand, found))
