"""Spiral (Dalfo-Fiol-Lopez-Martinez-Perez Section 3) equal-area layout explorer.

Tiles are (l, r, b, t).  Rule (derived from the source's Table 3):
 R1 = [1-x,1] x [0, 1/(k x)]                       (bottom wall, right corner)
 R2: on bottom wall between left wall and R1, grows up
 R3: on left wall between R2 and top wall, grows right
 R4: on top wall between R3 and right wall, grows down
 R5: on right wall between R1 and R4, grows left
 j>=6: outer neighbour R_{j-5}, stoppers R_{j-4} and R_{j-1}; class j mod 4 as below.
Closure residual: inner edge of R_k minus facing edge of R_{k-2}.
All arithmetic in a caller-chosen number type (float or Decimal).
"""
import sys
from decimal import Decimal, getcontext


def build(k, x, one=1.0):
    A = one / k
    T = {}
    T[1] = (one - x, one, 0 * one, A / x)
    l1 = T[1][0]
    T[2] = (0 * one, l1, 0 * one, A / l1)
    h = one - T[2][3]
    T[3] = (0 * one, A / h, T[2][3], one)
    w = one - T[3][1]
    T[4] = (T[3][1], one, one - A / w, one)
    for j in range(5, k + 1):
        c = j % 4
        if c == 1:
            X = one if j == 5 else T[j - 5][0]
            lo, hi = T[j - 4][3], T[j - 1][2]
            H = hi - lo
            if H <= 0:
                return None
            T[j] = (X - A / H, X, lo, hi)
        elif c == 2:
            Y = T[j - 5][3]
            lo, hi = T[j - 4][1], T[j - 1][0]
            W = hi - lo
            if W <= 0:
                return None
            T[j] = (lo, hi, Y, Y + A / W)
        elif c == 3:
            X = T[j - 5][1]
            lo, hi = T[j - 1][3], T[j - 4][2]
            H = hi - lo
            if H <= 0:
                return None
            T[j] = (X, X + A / H, lo, hi)
        else:
            Y = T[j - 5][2]
            lo, hi = T[j - 1][1], T[j - 4][0]
            W = hi - lo
            if W <= 0:
                return None
            T[j] = (lo, hi, Y - A / W, Y)
    return T


def residual(k, T):
    j = k
    c = j % 4
    f = T[j - 2]
    if c == 1:
        return T[j][0] - f[1]
    if c == 2:
        return T[j][3] - f[2]
    if c == 3:
        return T[j][1] - f[0]
    return T[j][2] - f[3]


def is_tiling(T, one, eps):
    ts = list(T.values())
    for (l, r, b, t) in ts:
        if not (l > -eps and r < one + eps and b > -eps and t < one + eps and r - l > eps and t - b > eps):
            return False
    for i in range(len(ts)):
        for j in range(i + 1, len(ts)):
            a, c = ts[i], ts[j]
            ox = min(a[1], c[1]) - max(a[0], c[0])
            oy = min(a[3], c[3]) - max(a[2], c[2])
            if ox > eps and oy > eps:
                return False
    return True


def scan(k, N=4000):
    """Find sign changes of residual on (0,1) where layout is defined."""
    roots = []
    prev = None
    for i in range(1, N):
        x = i / N
        T = build(k, x)
        if T is None:
            prev = None
            continue
        try:
            r = residual(k, T)
        except ZeroDivisionError:
            prev = None
            continue
        if prev is not None and (prev[1] > 0) != (r > 0):
            roots.append((prev[0], x))
        prev = (x, r)
    return roots


def refine(k, a, b, one=1.0, iters=200):
    fa = residual(k, build(k, a * one if one != 1.0 else a, one))
    a = a * one if one != 1.0 else a
    b = b * one if one != 1.0 else b
    for _ in range(iters):
        m = (a + b) / 2
        T = build(k, m, one)
        if T is None:
            return None
        fm = residual(k, T)
        if (fm > 0) == (fa > 0):
            a, fa = m, fm
        else:
            b = m
    return (a + b) / 2


def long_sides(T):
    return sorted(max(r - l, t - b) for (l, r, b, t) in T.values())


def proper(T, eps):
    xs = sorted(set([v for q in T.values() for v in (q[0], q[1])]))
    ys = sorted(set([v for q in T.values() for v in (q[2], q[3])]))
    # merge near-equal coordinates
    def merge(v):
        out = []
        for a in v:
            if not out or a - out[-1] > eps:
                out.append(a)
        return out
    xs, ys = merge(xs), merge(ys)
    ts = list(T.values())
    k = len(ts)
    bad = []
    for i1 in range(len(xs)):
        for i2 in range(i1 + 1, len(xs)):
            for j1 in range(len(ys)):
                for j2 in range(j1 + 1, len(ys)):
                    L, R, B, U = xs[i1], xs[i2], ys[j1], ys[j2]
                    inside = 0
                    ok = True
                    for (l, r, b, t) in ts:
                        if l > L - eps and r < R + eps and b > B - eps and t < U + eps:
                            inside += 1
                            continue
                        ox = min(r, R) - max(l, L)
                        oy = min(t, U) - max(b, B)
                        if ox > eps and oy > eps:
                            ok = False
                            break
                    if ok and 1 < inside < k:
                        bad.append((L, R, B, U, inside))
    return bad


if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for k in range(lo, hi + 1):
        rs = scan(k)
        out = []
        for (a, b) in rs:
            x = refine(k, a, b)
            if x is None:
                continue
            T = build(k, x)
            ok = is_tiling(T, 1.0, 1e-12)
            if not ok:
                continue
            ls = long_sides(T)
            gap = min(ls[i + 1] - ls[i] for i in range(len(ls) - 1))
            out.append((round(x, 10), 'mingap=%.3e' % gap))
        print(k, out, flush=True)
