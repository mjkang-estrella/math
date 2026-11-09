"""Line-count parity utilities for finite point sets (any dimension).

n_S(l) = number of affine lines parallel to l meeting S.  For a secant
direction l, n_S(l) = |S| - sum over occupied lines L (|S cap L| - 1).
Non-secant directions have n_S = |S|.

Exact mode: rational coordinates (Fraction or int); direction key is the
primitive integer vector with positive first nonzero entry.
Float mode: direction key is the rounded normalized vector (exploration only).
"""
from fractions import Fraction
from math import gcd
from itertools import combinations


def _prim(v):
    den = 1
    for x in v:
        if isinstance(x, Fraction):
            den = den * x.denominator // gcd(den, x.denominator)
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = gcd(g, abs(x))
    w = [x // g for x in w]
    for x in w:
        if x != 0:
            if x < 0:
                w = [-y for y in w]
            break
    return tuple(w)


def _fkey(v, digits=7):
    import math
    n = math.sqrt(sum(x * x for x in v))
    w = [x / n for x in v]
    for x in w:
        if abs(x) > 1e-9:
            if x < 0:
                w = [-y for y in w]
            break
    return tuple(round(x, digits) + 0.0 for x in w)


def direction_counts(S, exact=True, digits=7):
    """Return dict direction_key -> n_S(direction) for all secant directions."""
    S = list(S)
    n = len(S)
    pairs = {}
    for i, j in combinations(range(n), 2):
        v = [b - a for a, b in zip(S[i], S[j])]
        k = _prim(v) if exact else _fkey(v, digits)
        pairs.setdefault(k, []).append((i, j))
    out = {}
    for k, ps in pairs.items():
        parent = {}

        def f(x):
            while parent.get(x, x) != x:
                parent[x] = parent.get(parent[x], parent[x])
                x = parent[x]
            return x
        for i, j in ps:
            parent.setdefault(i, i)
            parent.setdefault(j, j)
            a, b = f(i), f(j)
            if a != b:
                parent[a] = b
        pts = set(parent)
        comps = len({f(x) for x in pts})
        out[k] = n - (len(pts) - comps)
    return out


def odd_directions(S, exact=True, digits=7):
    S = list(S)
    dc = direction_counts(S, exact, digits)
    odd = [k for k, c in dc.items() if c % 2]
    if len(S) % 2:
        odd.append('generic')
    return odd


def affine_dim(S):
    import sympy
    S = list(S)
    M = sympy.Matrix([[sympy.nsimplify(x) for x in p] + [1] for p in S])
    return M.rank() - 1
