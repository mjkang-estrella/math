"""Shared exact helpers (Fractions / mod-p ints). No floating point."""
from fractions import Fraction
from itertools import combinations_with_replacement


def quad_monomials(n):
    """Exponent tuples of degree-2 monomials in n variables, fixed order."""
    out = []
    for i, j in combinations_with_replacement(range(n), 2):
        e = [0] * n
        e[i] += 1
        e[j] += 1
        out.append(tuple(e))
    return out


def quartic_monomials(n):
    out = []
    for c in combinations_with_replacement(range(n), 4):
        e = [0] * n
        for i in c:
            e[i] += 1
        out.append(tuple(e))
    return out


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def mult_image(G, n):
    """v^T G v as dict quartic-exponent -> coefficient (G is N x N symmetric)."""
    v = quad_monomials(n)
    out = {}
    for a in range(len(v)):
        for b in range(len(v)):
            if G[a][b]:
                k = add(v[a], v[b])
                out[k] = out.get(k, 0) + G[a][b]
    return {k: c for k, c in out.items() if c}


def rank_mod_p(rows, p):
    rows = [[x % p for x in r] for r in rows]
    rank, col = 0, 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], p - 2, p)
        rows[rank] = [(x * inv) % p for x in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col]:
                f = rows[r][col]
                rows[r] = [(x - f * y) % p for x, y in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def nullspace_Q(rows, ncols):
    """Exact basis of {x : rows x = 0} over Q."""
    A = [[Fraction(x) for x in r] for r in rows]
    pivcols, rank = [], 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(A)) if A[r][col] != 0), None)
        if piv is None:
            continue
        A[rank], A[piv] = A[piv], A[rank]
        pv = A[rank][col]
        A[rank] = [x / pv for x in A[rank]]
        for r in range(len(A)):
            if r != rank and A[r][col] != 0:
                f = A[r][col]
                A[r] = [x - f * y for x, y in zip(A[r], A[rank])]
        pivcols.append(col)
        rank += 1
    free = [c for c in range(ncols) if c not in pivcols]
    basis = []
    for fc in free:
        x = [Fraction(0)] * ncols
        x[fc] = Fraction(1)
        for r, pc in enumerate(pivcols):
            x[pc] = -A[r][fc]
        basis.append(x)
    return basis


def charpoly(M):
    """Exact characteristic polynomial det(tI - M) coefficients, leading first (Faddeev-LeVerrier)."""
    n = len(M)
    I = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    coeffs = [Fraction(1)]
    Mk = [row[:] for row in I]
    for k in range(1, n + 1):
        AM = [[sum(M[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        c = -sum(AM[i][i] for i in range(n)) / k
        coeffs.append(c)
        Mk = [[AM[i][j] + (c if i == j else 0) for j in range(n)] for i in range(n)]
    return coeffs


def inertia_symmetric(M):
    """(n_pos, n_neg, n_zero) for an exact symmetric matrix: all eigenvalues are real,
    so Descartes' rule of signs is exact on det(tI-M) and on det(-tI-M)."""
    c = charpoly(M)
    n = len(M)
    nz = 0
    while nz < len(c) and c[len(c) - 1 - nz] == 0:
        nz += 1
    core = c[: len(c) - nz]

    def changes(seq):
        s = [x for x in seq if x != 0]
        return sum(1 for a, b in zip(s, s[1:]) if (a > 0) != (b > 0))

    deg = len(core) - 1
    pos = changes(core)
    neg = changes([x * (-1) ** (deg - i) for i, x in enumerate(core)])
    assert pos + neg + nz == n
    return pos, neg, nz
