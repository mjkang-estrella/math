# Independent exact checker for the hypercube Voronoi game (Stylianou arXiv:2510.25392, Sec. 1),
# written from the definitions for lane voronoi-proof-r1 (not derived from r134 vor.py).
#
# Game: voters at every vertex of Q_n = {0,1}^n; voter x gives its vote to the players at minimum
# Hamming distance, split equally among them (co-located players count separately).  Score of a
# player = 2^-n * sum of its vote shares.  Equilibrium: no player can strictly increase its score
# by moving to any vertex (occupied or not) while the others stay.
#
# Subspace profile: multiplicity vector m = (m_1..m_7) indexed by the nonzero functionals
# f in {1..7} on F_2^3 (f(a) = parity of popcount(f & a)).  Coordinates are grouped into classes;
# class f has m_f coordinates, and player a in F_2^3 sits at the point whose class-f coordinates
# all equal f(a).
# All arithmetic is exact: scores are returned as integers  L * (2^n * score)  with L = 840.
import sys as _sys
_sys.path.append("/home/mj-kang/.local/lib/python3.14/site-packages")  # user-site numpy (python3 -I disables user site)
import numpy as np
from math import comb
from fractions import Fraction

L = 840  # lcm(1..8)


def fval(f, a):
    return bin(f & a).count('1') & 1


def coords(m):
    """list of functionals, one per coordinate (coordinate j <-> bit j)."""
    out = []
    for f in range(1, 8):
        out += [f] * m[f - 1]
    return out


def positions(m):
    cs = coords(m)
    return [sum(fval(f, a) << j for j, f in enumerate(cs)) for a in range(8)]


def popcnt(x):
    return np.bitwise_count(x).astype(np.int64)


def voter_table(n, others):
    """for every voter x: (mu, tau) = (min distance to others, number of others at that distance)."""
    x = np.arange(1 << n, dtype=np.int64)
    D = np.stack([popcnt(x ^ p) for p in others])
    mu = D.min(axis=0)
    tau = (D == mu).sum(axis=0)
    return x, mu, tau


def score_brute(n, others, v, tab=None):
    """exact L*2^n*score of a player placed at v against `others` (direct sum over all voters)."""
    x, mu, tau = tab if tab is not None else voter_table(n, others)
    d = popcnt(x ^ v)
    win = d < mu
    tie = d == mu
    share = (L // (1 + tau))
    return int(win.sum()) * L + int((share * tie).sum())


def wht(a):
    a = a.copy()
    N = a.shape[0]
    h = 1
    while h < N:
        b = a.reshape(-1, 2, h)
        x = b[:, 0, :] + b[:, 1, :]
        y = b[:, 0, :] - b[:, 1, :]
        a = np.stack([x, y], axis=1).reshape(N)
        h *= 2
    return a


def kraw(n):
    """K[r][w] = sum_i (-1)^i C(w,i) C(n-w,r-i)  (WHT of the radius-r sphere at a weight-w point)."""
    return [[sum((-1) ** i * comb(w, i) * comb(n - w, r - i) for i in range(r + 1)) for w in range(n + 1)]
            for r in range(n + 1)]


def scores_all(n, others):
    """exact L*2^n*score of a player moved to v, for ALL v at once, via sphere convolutions.
    sigma(v) = sum_r (Phi_r * Sph_r)(v),  Phi_r(x) = L*share of a player at distance r from x.
    int64 arithmetic is exact modulo 2^64 and the true result N*sigma < 2^63, so wraparound is harmless."""
    N = 1 << n
    x, mu, tau = voter_table(n, others)
    K = kraw(n)
    w = popcnt(x)
    tot = np.zeros(N, dtype=np.int64)
    share_tie = (L // (1 + tau)).astype(np.int64)
    for r in range(0, int(mu.max()) + 1):
        phi = np.where(r < mu, L, np.where(r == mu, share_tie, 0)).astype(np.int64)
        if not phi.any():
            continue
        kr = np.array(K[r], dtype=np.int64)[w]
        with np.errstate(over='ignore'):
            tot += wht(phi) * kr
    with np.errstate(over='ignore'):
        S = wht(tot)
    assert np.all(S % N == 0)
    return S // N


def frac(s, n):
    return Fraction(int(s), L << n)
