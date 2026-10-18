"""Reviewer finite diagnostics for the T314C contribution review.

Independent implementation (no author code imported). Exact integer arithmetic only.
Certifies finite instances and implementation behaviour, not any uniform theorem,
proof gate or contribution verdict.

Checks:
  A. Every nonzero functional of beta(x,y)=x*y^p-x^p*y on F_(p^d) gives an
     alternating form of rank d-1 (Gow-Quinlan constant rank), zero common
     radical, span beta(L,L)=L.
  B. Exponent-p comparator E_(p,n): L x L with (x,a)(y,b)=(x+y,a+b+beta(x,y)/2).
     Its cyclic length is trivially 2n. Its sectional rank equals
     n + max_U (dim U - dim span beta(U,U)), computed over all subspaces U.
  C. Order-729 groups by breadth-first search over cyclic subnormal extensions
     K -> K<g>, g in N(K): exact ell(.,1) and max d(H) over all subgroups for
     the powerful group G_(3,3), its abelian comparator, and E_(3,3).
  D. Negative controls on the checker itself.
"""
import itertools, json, sys
from collections import deque


# ---------- finite field F_(p^d) ----------
def poly_mulmod(a, b, mod, p):
    d = len(mod) - 1
    r = [0] * (2 * d - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % p
    for k in range(len(r) - 1, d - 1, -1):
        c = r[k]
        if c:
            for j in range(d + 1):
                r[k - d + j] = (r[k - d + j] - c * mod[j]) % p
    return tuple(r[:d])


def is_irreducible(mod, p):
    d = len(mod) - 1
    # brute force: no root-free factorisation check needed for d<=5 via exhaustive monic divisors
    for deg in range(1, d // 2 + 1):
        for coeffs in itertools.product(range(p), repeat=deg):
            div = list(coeffs) + [1]
            # polynomial remainder of mod by div
            r = list(mod)
            for k in range(len(r) - 1, deg - 1, -1):
                c = r[k]
                if c:
                    for j in range(deg + 1):
                        r[k - deg + j] = (r[k - deg + j] - c * div[j]) % p
            if not any(r[:deg]):
                return False
    return True


def find_modulus(p, d):
    for coeffs in itertools.product(range(p), repeat=d):
        mod = list(coeffs) + [1]
        if mod[0] and is_irreducible(mod, p):
            return mod
    raise RuntimeError('no irreducible')


class Field:
    def __init__(self, p, d):
        self.p, self.d = p, d
        self.mod = find_modulus(p, d)
        self.elements = list(itertools.product(range(p), repeat=d))

    def mul(self, a, b):
        return poly_mulmod(a, b, self.mod, self.p)

    def pow(self, a, e):
        r = tuple([1] + [0] * (self.d - 1))
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def sub(self, a, b):
        return tuple((x - y) % self.p for x, y in zip(a, b))

    def basis(self):
        return [tuple(1 if i == j else 0 for j in range(self.d)) for i in range(self.d)]


def beta_field(F):
    p = F.p
    cache = {}

    def beta(x, y):
        key = (x, y)
        if key not in cache:
            cache[key] = F.sub(F.mul(x, F.pow(y, p)), F.mul(F.pow(x, p), y))
        return cache[key]
    return beta


def rank_mod_p(rows, p):
    m = [list(r) for r in rows]
    rank, col, ncols = 0, 0, (len(m[0]) if m else 0)
    while rank < len(m) and col < ncols:
        piv = next((i for i in range(rank, len(m)) if m[i][col] % p), None)
        if piv is None:
            col += 1
            continue
        m[rank], m[piv] = m[piv], m[rank]
        inv = pow(m[rank][col], p - 2, p)
        m[rank] = [(v * inv) % p for v in m[rank]]
        for i in range(len(m)):
            if i != rank and m[i][col] % p:
                c = m[i][col]
                m[i] = [(a - c * b) % p for a, b in zip(m[i], m[rank])]
        rank += 1
        col += 1
    return rank


def check_A(p, d, rank_fn=rank_mod_p):
    F = Field(p, d)
    beta = beta_field(F)
    B = F.basis()
    table = [[beta(B[i], B[j]) for j in range(d)] for i in range(d)]
    ranks = set()
    for c in itertools.product(range(p), repeat=d):
        if not any(c):
            continue
        M = [[sum(ci * vi for ci, vi in zip(c, table[i][j])) % p for j in range(d)] for i in range(d)]
        assert all(M[i][j] == (-M[j][i]) % p for i in range(d) for j in range(d))
        ranks.add(rank_fn(M, p))
    span = rank_fn([table[i][j] for i in range(d) for j in range(d)], p)
    # common radical: x with beta(x,B_j)=0 for all j
    common = [x for x in F.elements if any(x) and all(not any(beta(x, b)) for b in B)]
    return {'p': p, 'd': d, 'modulus': F.mod, 'functional_ranks': sorted(ranks),
            'span_dim': span, 'common_radical_nonzero': len(common)}


# ---------- subspace enumeration (RREF) ----------
def all_subspaces(p, n):
    out = [()]
    for k in range(1, n + 1):
        for pivots in itertools.combinations(range(n), k):
            free = [(r, c) for r in range(k) for c in range(n) if c > pivots[r] and c not in pivots]
            for vals in itertools.product(range(p), repeat=len(free)):
                rows = [[0] * n for _ in range(k)]
                for r in range(k):
                    rows[r][pivots[r]] = 1
                for (r, c), v in zip(free, vals):
                    rows[r][c] = v
                out.append(tuple(tuple(r) for r in rows))
    return out


def check_B(p, n):
    F = Field(p, n)
    beta = beta_field(F)
    subs = all_subspaces(p, n)
    best = None
    for U in subs:
        u = len(U)
        imgs = [beta(U[i], U[j]) for i in range(u) for j in range(i + 1, u)]
        m = rank_mod_p(imgs, p) if imgs else 0
        val = u - m
        best = val if best is None else max(best, val)
    srank = n + best
    return {'p': p, 'n': n, 'subspaces': len(subs), 'sectional_rank': srank,
            'cyclic_length': 2 * n, 'excess': 2 * n - srank,
            'proved_bounds_hold': n + 1 <= srank <= (3 * n - 1) // 2}


# ---------- order-729 groups ----------
def build_group(kind, p=3, d=3):
    F = Field(p, d)
    beta = beta_field(F) if kind != 'abelian' else (lambda x, y: (0,) * d)
    half = pow(2, p - 2, p)
    if kind in ('powerful', 'abelian'):
        q = p * p
        elems = list(itertools.product(range(q), repeat=d))
        idx = {e: i for i, e in enumerate(elems)}

        def mul(x, y):
            b = beta(tuple(v % p for v in x), tuple(v % p for v in y))
            return tuple((a + c + p * ((half * bb) % p)) % q for a, c, bb in zip(x, y, b))
    else:  # exponent-p comparator on L x L
        elems = list(itertools.product(range(p), repeat=2 * d))
        idx = {e: i for i, e in enumerate(elems)}

        def mul(x, y):
            b = beta(x[:d], y[:d])
            return tuple((a + c) % p for a, c in zip(x[:d], y[:d])) + \
                tuple((a + c + half * bb) % p for a, c, bb in zip(x[d:], y[d:], b))
    N = len(elems)
    T = [[idx[mul(elems[i], elems[j])] for j in range(N)] for i in range(N)]
    e = idx[tuple([0] * len(elems[0]))]
    inv = [next(j for j in range(N) if T[i][j] == e) for i in range(N)]
    # Associativity is proved in prose (bilinear correction cocycle); here only a deterministic
    # stride sample of 41^3 triples is checked.
    sample = range(0, N, 18)
    assert all(T[T[a][b]][c] == T[a][T[b][c]] for a in sample for b in sample for c in sample)
    return {'N': N, 'T': T, 'e': e, 'inv': inv, 'p': p}


def closure(G, gens):
    T, e = G['T'], G['e']
    S = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = T[x][g]
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def bfs_cyclic(G, require_normal=True):
    T, e, inv, N = G['T'], G['e'], G['inv'], G['N']
    start = frozenset([e])
    dist = {start: 0}
    gens = {start: []}
    q = deque([start])
    while q:
        K = q.popleft()
        for g in range(N):
            if g in K:
                continue
            if require_normal:
                if any(T[T[g][k]][inv[g]] not in K for k in K):
                    continue
                H = set(K)
                x = g
                while x not in K:
                    H.update(T[k][x] for k in K)
                    x = T[x][g]
                H = frozenset(H)
            else:
                H = closure(G, gens[K] + [g])
            if H not in dist:
                dist[H] = dist[K] + 1
                gens[H] = gens[K] + [g]
                q.append(H)
    return dist, gens


def frattini_rank(G, H, gens):
    T, inv, p = G['T'], G['inv'], G['p']

    def power(x, m):
        r = G['e']
        for _ in range(m):
            r = T[r][x]
        return r
    phi_gens = [power(g, p) for g in gens]
    phi_gens += [T[T[T[a][b]][inv[a]]][inv[b]] for a in gens for b in gens]
    Phi = closure(G, phi_gens)
    q = len(H) // len(Phi)
    r = 0
    while q > 1:
        assert q % p == 0
        q //= p
        r += 1
    return r


def check_C(kind):
    G = build_group(kind)
    dist, gens = bfs_cyclic(G)
    full = frozenset(range(G['N']))
    srank = max(frattini_rank(G, H, gens[H]) for H in dist)
    return {'group': kind, 'order': G['N'], 'subgroups': len(dist),
            'ell': dist[full], 'sectional_rank': srank}, G


def main():
    out = {'A': [check_A(3, 3), check_A(3, 5), check_A(5, 3), check_A(7, 3)]}
    for r in out['A']:
        assert r['functional_ranks'] == [r['d'] - 1], r
        assert r['span_dim'] == r['d'] and r['common_radical_nonzero'] == 0, r
    out['B'] = [check_B(3, 3), check_B(3, 5), check_B(5, 3)]
    for r in out['B']:
        assert r['proved_bounds_hold'], r
    C = {}
    for kind in ('powerful', 'abelian', 'exponent-p'):
        res, G = check_C(kind)
        C[kind] = (res, G)
    out['C'] = [C[k][0] for k in C]
    assert C['powerful'][0]['ell'] == 4 and C['powerful'][0]['sectional_rank'] == 3
    assert C['abelian'][0]['ell'] == 3
    assert C['exponent-p'][0]['ell'] == 6 and C['exponent-p'][0]['sectional_rank'] == 4
    # D. negative controls on the checker
    controls = []
    # D1: a rank routine that silently drops the last row must be caught by check A
    bad_rank = lambda rows, p: rank_mod_p(rows[:-1], p)
    r = check_A(3, 3, rank_fn=bad_rank)
    controls.append({'control': 'truncated-rank-routine', 'detected': r['functional_ranks'] != [2] or r['span_dim'] != 3})
    # D2: dropping the normality requirement changes the computed length (so the check is not vacuous)
    G = C['powerful'][1]
    dist, _ = bfs_cyclic(G, require_normal=False)
    controls.append({'control': 'no-normality-bfs', 'mutated_ell': dist[frozenset(range(G['N']))],
                     'detected': dist[frozenset(range(G['N']))] != 4})
    # D3: degenerate beta (image in one line) has a zero scalar form; the d+rho bound drops to d
    F = Field(3, 3)
    B = F.basis()
    deg_ranks = set()
    for c in itertools.product(range(3), repeat=3):
        if any(c):
            M = [[(c[0] * ((1 if (i, j) == (0, 1) else -1 if (i, j) == (1, 0) else 0) % 3)) % 3 for j in range(3)] for i in range(3)]
            deg_ranks.add(rank_mod_p(M, 3))
    controls.append({'control': 'degenerate-beta-min-rank-zero', 'detected': min(deg_ranks) == 0})
    for c in controls:
        assert c['detected'], c
    out['D'] = controls
    out['limits'] = ('finite instances and checker controls only; no uniform proof, '
                     'no proof gate, no contribution verdict')
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
