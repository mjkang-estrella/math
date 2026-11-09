"""Independent spider-state solver built only from Prop 6.1 (with (N1)-(N3)) and Thm 4.3.

Statuses: 'n','i','o','f'.  Directions on a leg: 'I' (towards centre), 'O' (away).
Far end of an attached leg: 'F' (free), 'I', 'O'.
A state is (s, L) with L a sorted tuple of (h, phi), h >= 1.
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)


def A(k): return k % 2
def B(k): return k
def C(k): return k % 2
def D(k): return 1 if (k >= 2 and k % 2 == 0) else 0


def rho(h, delta, phi):
    """detached run, near end blocked in direction delta, far end phi"""
    if phi == 'F':
        return B(h)
    return C(h) if phi == delta else D(h)


def rho_free(h, phi):
    return A(h) if phi == 'F' else B(h)


def sdot(s, delta):
    # status of centre after an arc pointing into (I) / out of (O) the centre
    if delta == 'I':
        return {'n': 'i', 'i': 'i', 'o': 'f', 'f': 'f'}[s]
    return {'n': 'o', 'o': 'o', 'i': 'f', 'f': 'f'}[s]


def mex(S):
    m = 0
    while m in S:
        m += 1
    return m


@lru_cache(maxsize=None)
def Gamma(s, L):
    L = tuple(sorted(L))
    if len(L) == 0:                      # (N3)
        return 0
    if s == 'f':                         # (N1)
        v = 0
        for (h, phi) in L:
            v ^= rho_free(h, phi)
        return v
    if s in ('i', 'o') and len(L) == 1:  # (N2)
        (h, phi), = L
        return rho(h, 'O' if s == 'i' else 'I', phi)
    return mex(options(s, L))


def norm(L):
    return tuple(sorted(L))


@lru_cache(maxsize=None)
def options(s, L):
    opts = set()
    seen = set()
    for idx, (h, phi) in enumerate(L):
        if (h, phi) in seen:
            continue
        seen.add((h, phi))
        rest = L[:idx] + L[idx + 1:]
        for j in range(1, h + 1):
            for delta in ('I', 'O'):
                if j == h and phi != 'F' and delta != phi:
                    continue
                det = rho(h - j, delta, phi)
                if j >= 2:
                    v = det ^ Gamma(s, norm(rest + ((j - 1, delta),)))
                else:
                    v = det ^ Gamma(sdot(s, delta), norm(rest))
                opts.add(v)
    return frozenset(opts)


def G(s, *legs):
    return Gamma(s, norm(legs))


def spider(*xs):
    return G('n', *[(x, 'F') for x in xs])
