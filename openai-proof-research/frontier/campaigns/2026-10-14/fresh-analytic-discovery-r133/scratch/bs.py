# MIT License. Author: Myeongjin Kang. Exploration helpers (float), not certificates.
import math, random

def Mspl(t, a):
    """Normalized B-spline density M(t|a) (integral 1), knots a sorted, degree len(a)-2. Cox-de Boor."""
    m = len(a); d = m - 2
    if t < a[0] or t >= a[-1]:
        return 0.0
    B = [1.0 if a[j] <= t < a[j + 1] else 0.0 for j in range(m - 1)]
    for k in range(1, d + 1):
        nb = []
        for j in range(m - 1 - k):
            v = 0.0
            den1 = a[j + k] - a[j]
            if den1 > 0: v += (t - a[j]) / den1 * B[j]
            den2 = a[j + k + 1] - a[j + 1]
            if den2 > 0: v += (a[j + k + 1] - t) / den2 * B[j + 1]
            nb.append(v)
        B = nb
    return (m - 1) / (a[-1] - a[0]) * B[0]

def D(a):
    s = sorted(a); m = len(s)
    return sum((2 * i - m + 1) * s[i] for i in range(m))

def maxM(a, iters=80):
    a = sorted(a)
    lo, hi = a[0], a[-1]
    g = (math.sqrt(5) - 1) / 2
    x1 = hi - g * (hi - lo); x2 = lo + g * (hi - lo)
    f1 = Mspl(x1, a); f2 = Mspl(x2, a)
    for _ in range(iters):
        if f1 < f2:
            lo = x1; x1 = x2; f1 = f2; x2 = lo + g * (hi - lo); f2 = Mspl(x2, a)
        else:
            hi = x2; x2 = x1; f2 = f1; x1 = hi - g * (hi - lo); f1 = Mspl(x1, a)
    t = (lo + hi) / 2
    return Mspl(t, a), t

def Phi(a):
    a = sorted(a); m = len(a)
    mm, t = maxM(a)
    return D(a) * mm / (m - 1) ** 2, t

GL5 = [(-0.9061798459386640, 0.2369268850561891), (-0.5384693101056831, 0.4786286704993665),
       (0.0, 0.5688888888888889), (0.5384693101056831, 0.4786286704993665), (0.9061798459386640, 0.2369268850561891)]

def moments(b):
    """For L=<b,p>, p uniform on simplex Delta^{n-1} (n=len(b)>=2): returns (E L^+, E L^-). Exact up to float
    (B-spline piecewise polynomial of degree n-2; 5-pt Gauss-Legendre on each knot interval, split at 0)."""
    b = sorted(b); n = len(b)
    pts = sorted(set(b + [0.0]))
    Ep = En = 0.0
    for lo, hi in zip(pts, pts[1:]):
        if hi <= lo: continue
        c = (lo + hi) / 2; h = (hi - lo) / 2
        for x, w in GL5:
            t = c + h * x
            v = Mspl(t, b) * w * h
            if t > 0: Ep += t * v
            else: En -= t * v
    return Ep, En

def rho(b):
    n = len(b)
    Ep, En = moments(b)
    return D(b) / (n * (n + 1) * (math.sqrt(Ep) + math.sqrt(En)) ** 2)
