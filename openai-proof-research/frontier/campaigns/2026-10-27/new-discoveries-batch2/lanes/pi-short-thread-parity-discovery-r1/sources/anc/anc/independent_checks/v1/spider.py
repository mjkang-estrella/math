"""Independent implementation of Theorem 4.3 (runs) and Proposition 6.1 (spider recursion).
Written by the referee from the paper's text only.

Statuses: 'n','i','o','f'.  Far ends / directions: 'F' (free), 'I' (towards centre), 'O' (away).
A spider state is (s, L) with L a sorted tuple of (h, phi), h >= 1.
"""
import sys
sys.setrecursionlimit(1 << 20)


def A(k): return k % 2
def B(k): return k
def C(k): return k % 2
def Dv(k): return 1 if (k >= 2 and k % 2 == 0) else 0


def rho(h, delta, phi):
    """detached run, near end blocked in direction delta, far end phi"""
    if phi == 'F':
        return B(h)
    if phi == delta:
        return C(h)
    return Dv(h)


def rho_free(h, phi):
    return A(h) if phi == 'F' else B(h)


def times(s, delta):
    """status of c after an arc at c pointing IN (delta='I' -> s.i) or OUT (s.o)"""
    if delta == 'I':
        return {'n': 'i', 'i': 'i', 'o': 'f', 'f': 'f'}[s]
    return {'n': 'o', 'o': 'o', 'i': 'f', 'f': 'f'}[s]


def mex(S):
    m = 0
    while m in S:
        m += 1
    return m


MEMO = {}


def Gamma(s, L):
    key = (s, L)
    v = MEMO.get(key)
    if v is not None:
        return v
    if len(L) == 0:                       # (N3)
        v = 0
    elif s == 'f':                         # (N1)
        v = 0
        for (h, phi) in L:
            v ^= rho_free(h, phi)
    elif s in ('i', 'o') and len(L) == 1:  # (N2)
        (h, phi), = L
        v = rho(h, 'O' if s == 'i' else 'I', phi)
    else:
        opts = set()
        for idx in range(len(L)):
            if idx > 0 and L[idx] == L[idx - 1]:
                continue
            h, phi = L[idx]
            rest = L[:idx] + L[idx + 1:]
            for j in range(1, h + 1):
                for delta in ('I', 'O'):
                    if j == h and phi != 'F' and delta != phi:
                        continue
                    det = rho(h - j, delta, phi)
                    if j >= 2:
                        nl = tuple(sorted(rest + ((j - 1, delta),)))
                        opts.add(det ^ Gamma(s, nl))
                    else:
                        opts.add(det ^ Gamma(times(s, delta), rest))
        v = mex(opts)
    MEMO[key] = v
    return v


def spider(*legs):
    return Gamma('n', tuple(sorted((x, 'F') for x in legs)))


def V(s, K, phi, r):
    return Gamma(s, tuple(sorted(tuple(K) + ((r, phi),))))
