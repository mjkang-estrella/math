#!/usr/bin/env python3
"""Exact polynomial computations for the Oh-Scrimshaw A.4 (even-shift q-Motzkin
Hankel positivity) problem. Bounded memory, exact dict-of-monomial arithmetic.

Recurrence (primary source, arXiv:1805.00113v1 Appendix A):
  M_0(q) = 1,
  M_{n+1}(q) = M_n(q) + sum_{r=0}^{n-1} q^{r+1} M_r(q) M_{n-1-r}(q).

Conjecture A.4: det[ M_{i+j+2k}(q) ]_{i,j=0}^{n-1} in Z>=0[q] for all k,n >= 1.
"""
import sys
from fractions import Fraction

# ---------------- exact polynomial arithmetic (dict exp->int coeff) ----------
def padd(a, b):
    r = dict(a)
    for e, c in b.items():
        if c:
            r[e] = r.get(e, 0) + c
            if r[e] == 0:
                del r[e]
    return r

def pmul(a, b):
    if not a or not b:
        return {}
    r = {}
    for e1, c1 in a.items():
        if len(a) * len(b) > 4_000_000:
            raise MemoryError("poly too large")
        for e2, c2 in b.items():
            e = e1 + e2
            r[e] = r.get(e, 0) + c1 * c2
    return {e: c for e, c in r.items() if c}

def pzero(a):
    return all(c >= 0 for c in a.values())

def pstr(a):
    if not a:
        return "0"
    return " + ".join(f"{c}q^{e}" for e, c in sorted(a.items()))

def psubst_shift(a, c):  # evaluate-free; scale q^m -> q^(m) ... not needed
    pass

# ---------------- moments ---------------------------------------------------
NMAX = 26
M = [None] * NMAX
M[0] = {0: 1}
for n in range(NMAX - 1):
    acc = M[n]
    for r in range(n):
        acc = padd(acc, pmul({r + 1: 1}, pmul(M[r], M[n - 1 - r])))
    M[n + 1] = acc
print("M_n for n=0..12:")
for n in range(13):
    print(f"M_{n} = {pstr(M[n])}")

# check M_3^2 relation etc.
print("M_2 =", pstr(M[2]), " M_3 =", pstr(M[3]))

# ---------------- Hankel determinants of [M_{i+j+r}] ------------------------
def hankel_det(r, n):
    """det [ M_{i+j+r} ]_{i,j=0}^{n-1} by fraction-free Bareiss over Q(q)."""
    rows = n
    # matrix of polys
    A = [[M[i + j + r] for j in range(rows)] for i in range(rows)]
    prev = {0: 1}  # previous pivot (poly) = 1
    sign = 1
    for k in range(rows - 1):
        # pivot
        if A[k][k] == {}:
            # find swap
            for i in range(k + 1, rows):
                if A[i][k] != {}:
                    A[k], A[i] = A[i], A[k]
                    sign = -sign
                    break
            else:
                return {}
        for i in range(k + 1, rows):
            for j in range(k + 1, rows):
                # A[i][j] = (A[k][k]*A[i][j] - A[i][k]*A[k][j]) / prev
                num = padd(pmul(A[k][k], A[i][j]), {0: 0})
                t1 = pmul(A[i][k], A[k][j])
                num = padd(num, {e: -c for e, c in t1.items()})
                if k == 0:
                    A[i][j] = num
                else:
                    # exact division by prev poly
                    A[i][j] = poly_divexact(num, prev)
        prev = A[k][k]
    return {e: c * sign for e, c in A[rows - 1][rows - 1].items()}

def poly_divexact(a, b):
    """exact division of polys with integer coeffs (b | a)."""
    a = dict(a); b = dict(b)
    if b == {0: 1}:
        return a
    q = {}
    db = max(b)
    cb = b[db]
    # normalize b monic? assume content divides; do it lazily over exponents sorted desc
    a = {e: c for e, c in a.items()}
    while a:
        da = max(a)
        if da < db:
            raise ValueError("not divisible")
        f = da - db
        # coefficient: must be integer
        ca = a[da]
        if ca % cb != 0:
            raise ValueError(f"coeff not divisible: {ca} / {cb}")
        cq = ca // cb
        q[f] = cq
        for e, c in b.items():
            e2 = e + f
            v = a.get(e2, 0) - cq * c
            if v == 0:
                a.pop(e2, None)
            else:
                a[e2] = v
    return q

# sanity: M_2 = 1+q etc. Verify Cigler shift-0 monomial:
for n in range(1, 8):
    d = hankel_det(0, n)
    print(f"Delta^{(0)}_{n} = {pstr(d)}")
