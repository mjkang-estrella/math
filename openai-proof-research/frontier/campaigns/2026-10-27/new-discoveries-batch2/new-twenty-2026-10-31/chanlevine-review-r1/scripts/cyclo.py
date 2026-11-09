"""Exact arithmetic in Z[z]/(Phi_e(z)) and in (Z[z]/Phi_e)[t].  Written for this review (no reuse)."""
from functools import lru_cache


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def ptrim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def pdivexact(a, b):
    """Exact division of integer polynomials, b monic."""
    a = ptrim(a)
    b = ptrim(b)
    assert b[-1] == 1
    q = [0] * max(1, len(a) - len(b) + 1)
    a = list(a)
    for k in range(len(a) - len(b), -1, -1):
        c = a[k + len(b) - 1]
        q[k] = c
        for j, y in enumerate(b):
            a[k + j] -= c * y
    assert not any(a), "not exact"
    return ptrim(q)


@lru_cache(maxsize=None)
def phi(e):
    num = [-1] + [0] * (e - 1) + [1]
    for d in range(1, e):
        if e % d == 0:
            num = pdivexact(num, list(phi(d)))
    return tuple(num)


class Cyc:
    """Element of Q(zeta_e) with integer coefficients, reduced modulo Phi_e."""
    __slots__ = ("e", "c")

    def __init__(self, e, c):
        self.e = e
        f = phi(e)
        deg = len(f) - 1
        c = list(c)
        for k in range(len(c) - 1, deg - 1, -1):
            a = c[k]
            if a:
                for j in range(deg + 1):
                    c[k - deg + j] -= a * f[j]
        c = c[:deg] + [0] * max(0, deg - len(c))
        self.c = tuple(c)

    @staticmethod
    def const(e, a):
        return Cyc(e, [a])

    @staticmethod
    def zpow(e, k):
        k %= e
        return Cyc(e, [0] * k + [1])

    def __add__(self, o):
        return Cyc(self.e, [a + b for a, b in zip(self.c, o.c)])

    def __sub__(self, o):
        return Cyc(self.e, [a - b for a, b in zip(self.c, o.c)])

    def __neg__(self):
        return Cyc(self.e, [-a for a in self.c])

    def __mul__(self, o):
        return Cyc(self.e, pmul(list(self.c), list(o.c)))

    def is_zero(self):
        return not any(self.c)

    def as_int(self):
        """Return the integer if the element is rational (constant), else None."""
        if any(self.c[1:]):
            return None
        return self.c[0]

    def __eq__(self, o):
        return self.e == o.e and self.c == o.c

    def __repr__(self):
        return "Cyc(%d,%s)" % (self.e, list(self.c))


# polynomials in t with Cyc coefficients: list index = power of t
def tp_add(a, b, e):
    n = max(len(a), len(b))
    z = Cyc.const(e, 0)
    return [(a[i] if i < len(a) else z) + (b[i] if i < len(b) else z) for i in range(n)]


def tp_sub(a, b, e):
    n = max(len(a), len(b))
    z = Cyc.const(e, 0)
    return [(a[i] if i < len(a) else z) - (b[i] if i < len(b) else z) for i in range(n)]


def tp_mul(a, b, e):
    if not a or not b:
        return []
    z = Cyc.const(e, 0)
    r = [z] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x.is_zero():
            continue
        for j, y in enumerate(b):
            if y.is_zero():
                continue
            r[i + j] = r[i + j] + x * y
    return r


def tp_trim(a):
    a = list(a)
    while a and a[-1].is_zero():
        a.pop()
    return a
