"""371606 diagnostic: enumerate automata on n states with alphabet of size <= A (letters = non-identity maps,
unordered sets), compute shortest reset word length (BFS on subsets), and for extremal ones ((n-1)^2)
test C-irreducibility of the sum-zero representation (Burnside dimension test mod two primes).
usage: extremal_check.py n A
"""
import sys, itertools
from collections import deque
n, A = int(sys.argv[1]), int(sys.argv[2])
PR = [1000000007, 998244353]
maps = [m for m in itertools.product(range(n), repeat=n) if m != tuple(range(n))]

def reset_len(letters):
    full = (1 << n) - 1
    dist = {full: 0}; dq = deque([full])
    while dq:
        S = dq.popleft()
        if S & (S - 1) == 0:
            return dist[S]
        for m in letters:
            T = 0
            for i in range(n):
                if S >> i & 1:
                    T |= 1 << m[i]
            if T not in dist:
                dist[T] = dist[S] + 1; dq.append(T)
    return None

def mat(m):
    M = [0] * ((n - 1) * (n - 1))
    for i in range(1, n):
        for s, sg in ((m[i], 1), (m[0], -1)):
            if s != 0:
                M[(i - 1) * (n - 1) + s - 1] += sg
    return M

def monoid(letters):
    idm = tuple(range(n)); seen = {idm}; st = [idm]
    while st:
        u = st.pop()
        for m in letters:
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

ext = red = 0
for a in range(1, A + 1):
    for letters in itertools.combinations(maps, a):
        L = reset_len(letters)
        if L != (n - 1) ** 2:
            continue
        ext += 1
        vecs = [mat(u) for u in monoid(letters)]
        if not all(rank_mod(vecs, p) == (n - 1) ** 2 for p in PR):
            red += 1
            print('REDUCIBLE EXTREMAL', letters)
print(f'n={n} alphabet<={A}: extremal={ext} reducible_extremal={red}')
