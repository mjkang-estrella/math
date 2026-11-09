#!/usr/bin/env python3
"""H014 exact enumeration prototype; stdlib only, no factoring/smoothness.

Coefficients are low degree first. All polynomial arithmetic is exact.
This standalone file is frozen before the single registered validation run.
"""
from fractions import Fraction as F
from math import gcd, isqrt, lcm


def trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [0]


def add(p, q):
    out = [0] * max(len(p), len(q))
    for i, x in enumerate(p):
        out[i] += x
    for i, x in enumerate(q):
        out[i] += x
    return trim(out)


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] += x * y
    return trim(out)


def value(p, x):
    out = 0
    for c in reversed(p):
        out = out * x + c
    return out


def derivative(p):
    return trim([i * p[i] for i in range(1, len(p))])


def divrem(p, q):
    p, q = list(map(F, trim(p))), list(map(F, trim(q)))
    if q == [0]:
        raise ZeroDivisionError("polynomial division by zero")
    out = [F(0)] * max(1, len(p) - len(q) + 1)
    while p != [0] and len(p) >= len(q):
        k = len(p) - len(q)
        c = p[-1] / q[-1]
        out[k] += c
        for i, v in enumerate(q):
            p[k + i] -= c * v
        p = trim(p)
    return trim(out), p


def primitive(p):
    """Multiply by a POSITIVE rational scalar only, preserving every sign."""
    p = list(map(F, trim(p)))
    den = lcm(*(x.denominator for x in p))
    ints = [int(x * den) for x in p]
    content = gcd(*ints)
    return [x // content for x in ints] if content else [0]


def pgcd(p, q):
    p, q = primitive(p), primitive(q)
    while q != [0]:
        p, q = q, primitive(divrem(p, q)[1])
    return primitive(p)


def squarefree(p):
    p = primitive(p)
    if len(p) == 1:
        return p
    q, r = divrem(p, pgcd(p, derivative(p)))
    assert r == [0]
    return primitive(q)


def sturm(p):
    p = squarefree(p)
    if len(p) == 1:
        return [p]
    seq = [p, primitive(derivative(p))]
    while True:
        r = primitive([-x for x in divrem(seq[-2], seq[-1])[1]])
        if r == [0]:
            return seq
        seq.append(r)


def side_sign(p, x, side):
    """Sign immediately left/right of x, including exact endpoint roots."""
    order = 0
    while p != [0]:
        v = value(p, x)
        if v:
            return (1 if v > 0 else -1) * (side if order % 2 else 1)
        p = derivative(p)
        order += 1
    return 0


def variations(seq, x, side):
    signs = [side_sign(p, x, side) for p in seq]
    signs = [s for s in signs if s]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def isolate(p, stats):
    """All DISTINCT real roots: exact points or closed rational intervals.

    Nonpoint intervals have width <= 1/4, nonroot endpoints, and one root.
    An iterative stack avoids a recursion-limit oracle on large inputs.
    """
    q = squarefree(p)
    if len(q) == 1:
        if q == [0]:
            raise ValueError("zero polynomial has no finite root isolation")
        return []
    seq = sturm(q)
    radius = 2 + max(abs(x) for x in q[:-1]) // abs(q[-1])

    def count(left, right):
        stats["sturm_counts"] = stats.get("sturm_counts", 0) + 1
        return variations(seq, left, 1) - variations(seq, right, -1)

    left, right = F(-radius), F(radius)
    stack = [(left, right, count(left, right), 0)]
    result = []
    while stack:
        left, right, number, depth = stack.pop()
        stats["isolation_nodes"] = stats.get("isolation_nodes", 0) + 1
        stats["max_depth"] = max(stats.get("max_depth", 0), depth)
        if not number:
            continue
        assert number > 0
        if (number == 1 and right - left <= F(1, 4)
                and value(q, left) and value(q, right)):
            result.append((left, right))
            continue
        mid = (left + right) / 2
        at_mid = value(q, mid) == 0
        if at_mid:
            result.append((mid, mid))
        nl, nr = count(left, mid), count(mid, right)
        assert nl + nr + int(at_mid) == number
        stack.append((mid, right, nr, depth + 1))
        stack.append((left, mid, nl, depth + 1))
    return sorted(result)


def ceilq(x):
    return -((-x.numerator) // x.denominator)


def accepted_ranges(p, threshold, lower, upper, stats=None):
    """Disjoint accepted integer ranges; rejected long ranges are not scanned."""
    if stats is None:
        stats = {}
    p = trim(p)
    if lower > upper or threshold < 0:
        return []
    if len(p) == 1:
        return [(lower, upper)] if abs(p[0]) <= threshold else []
    minus, plus = list(p), list(p)
    minus[0] -= threshold
    plus[0] += threshold
    # Union of the two boundary root sets; squarefree removes repeated roots,
    # including the complete duplication when threshold == 0.
    roots = isolate(mul(minus, plus), stats)
    out, cursor = [], lower
    for left, right in roots:
        end = min(upper, ceilq(left) - 1)
        if cursor <= end:
            stats["gap_tests"] = stats.get("gap_tests", 0) + 1
            if abs(value(p, cursor)) <= threshold:
                out.append((cursor, end))
        start = max(cursor, lower, ceilq(left))
        end = min(upper, right.numerator // right.denominator)
        # At most one integer: nonpoint widths <= 1/4; point intervals too.
        for k in range(start, end + 1):
            stats["boundary_tests"] = stats.get("boundary_tests", 0) + 1
            if abs(value(p, k)) <= threshold:
                out.append((k, k))
        cursor = max(cursor, right.numerator // right.denominator + 1)
    if cursor <= upper:
        stats["gap_tests"] = stats.get("gap_tests", 0) + 1
        if abs(value(p, cursor)) <= threshold:
            out.append((cursor, upper))
    return out


def determinant_bareiss(matrix):
    m = [row[:] for row in matrix]
    if not m:
        return 1
    n, sign, previous = len(m), 1, 1
    for k in range(n - 1):
        pivot_row = next((i for i in range(k, n) if m[i][k]), None)
        if pivot_row is None:
            return 0
        if pivot_row != k:
            m[k], m[pivot_row] = m[pivot_row], m[k]
            sign = -sign
        pivot = m[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                numerator = pivot * m[i][j] - m[i][k] * m[k][j]
                assert numerator % previous == 0
                m[i][j] = numerator // previous
            m[i][k] = 0
        previous = pivot
    return sign * m[-1][-1]


def quotient_resultant(f, g):
    """det(multiplication by g on Z[X]/(monic f)), also for repeated f."""
    assert f[-1] == 1
    d = len(f) - 1
    matrix = [[0] * d for _ in range(d)]
    for j in range(d):
        p = [0] * j + list(g)
        p += [0] * max(0, d - len(p))
        for k in range(len(p) - 1, d - 1, -1):
            coeff = p[k]
            for i in range(d + 1):
                p[k - d + i] -= coeff * f[i]
        for i in range(d):
            matrix[i][j] = p[i]
    return determinant_bareiss(matrix)


def line_polynomial(f, beta, gamma):
    d = len(f) - 1
    values = [quotient_resultant(f, [gamma + a, beta - 2 * a, a])
              for a in range(d + 1)]
    out, basis = [F(0)], [F(1)]
    for k in range(d + 1):
        out = add(out, [values[0] * c for c in basis])
        values = [b - a for a, b in zip(values, values[1:])]
        if k < d:
            basis = [c / (k + 1) for c in mul(basis, [-k, 1])]
    assert all(c.denominator == 1 for c in out)
    out = list(map(int, out))
    assert len(out) == d + 1 and out[-1] == sum(f) ** 2
    return out


def integer_root(number, degree):
    assert number >= 0 and degree >= 1
    lo, hi = 0, 1 << ((number.bit_length() + degree - 1) // degree)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid ** degree <= number:
            lo = mid
        else:
            hi = mid - 1
    return lo


def threshold_for(N, f, height, n_power=6):
    d, A = len(f) - 1, max(abs(x) for x in f)
    c0 = (3 * height) ** d * (d + 1) * A * A
    power = 5 * d
    threshold = integer_root(c0 ** power // N ** n_power, power)
    assert threshold ** power * N ** n_power <= c0 ** power
    assert (threshold + 1) ** power * N ** n_power > c0 ** power
    return threshold, c0


def base_polynomial(N, degree):
    m = integer_root(N, degree)
    if m < 2:
        raise ValueError("base below two")
    digits, q = [], N
    while q:
        q, digit = divmod(q, m)
        digits.append(digit)
    if len(digits) != degree + 1 or digits[-1] != 1:
        raise ValueError("requested ordinary base polynomial is not monic degree d")
    return m, digits


def enumerate_sublevel(f, height, threshold, stats=None):
    if stats is None:
        stats = {}
    if height < 1 or len(f) < 2 or f[-1] != 1 or min(f) < 0:
        raise ValueError("need H>=1, monic positive-degree nonnegative f")
    # Symmetric rectangle covers every positive-leading cube label.
    for beta in range(-3 * height, 3 * height + 1):
        for gamma in range(-2 * height, 2 * height + 1):
            stats["labels"] = stats.get("labels", 0) + 1
            lower = max(1, -((height - beta) // 2), -height - gamma)
            upper = min(height, (beta + height) // 2, height - gamma)
            if lower > upper:
                continue
            stats["nonempty_lines"] = stats.get("nonempty_lines", 0) + 1
            p = line_polynomial(f, beta, gamma)
            for lo, hi in accepted_ranges(p, threshold, lower, upper, stats):
                for a in range(lo, hi + 1):
                    stats["emitted"] = stats.get("emitted", 0) + 1
                    yield a, beta - 2 * a, gamma + a


def primitive_irreducible(g):
    a, b, c = g
    if gcd(a, b, c) != 1:
        return False
    disc = b * b - 4 * a * c
    return disc < 0 or isqrt(disc) ** 2 != disc
