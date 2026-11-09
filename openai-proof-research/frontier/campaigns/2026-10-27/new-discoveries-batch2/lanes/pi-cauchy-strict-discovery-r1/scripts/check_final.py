"""Verification v6 — final fast diagnostics.

A. Integral representation via J (v-substitution quadrature, with explicit tail bound).
B. Discrete Andreief / Cauchy-Binet (fixed scalar accumulation).
C. (already done in v5) D_x asymptotics -> ratio 1.  D. (already done) hp minors.
"""
import mpmath as mp
import numpy as np
import itertools as it
from falpha import falpha, K

mp.mp.dps = 30


def ck(k, alpha):
    return (-1) ** (k + 1) * mp.gamma(1 + alpha * k) * mp.sin(mp.pi * alpha * k) / (mp.pi * mp.factorial(k))


def fser(z, alpha, KMAX=600):
    z = mp.mpf(z); alpha = mp.mpf(alpha)
    return mp.fsum([ck(k, alpha) * z ** (-alpha * k - 1) for k in range(1, KMAX + 1)])


def finv(z, alpha):
    a = mp.mpf(alpha)
    return mp.invertlaplace(lambda lam: mp.e ** (-lam ** a), mp.mpf(z), method='talbot')


def J_quad(d, alpha, zlo=mp.mpf('0.01')):
    """J(d) = int_0^inf v f(e^{d/2} v) f(e^{-d/2} v) dv, series valid when both args >= zlo."""
    d = mp.mpf(d); alpha = mp.mpf(alpha)
    vlo = zlo * mp.e ** (abs(d) / 2)
    g = lambda v: v * fser(mp.e ** (d / 2) * v, alpha) * fser(mp.e ** (-d / 2) * v, alpha)
    val = mp.quad(g, [vlo, '0.1', '1', '10', '100', '1e4', '1e6'])
    # tail bound below vlo: f increasing on (0, mode], both args <= zlo*something small;
    # use f(e^{-|d|/2} v) <= f(zlo * e^{-|d|}) computed via invertlaplace (astronomically small)
    fz = finv(zlo * mp.e ** (-abs(d)), alpha)
    tail = vlo ** 2 / 2 * fz ** 2
    return val, tail


def J_closed(d, alpha):
    d = mp.mpf(d); alpha = mp.mpf(alpha)
    return mp.sin(mp.pi * alpha) / (2 * mp.pi * (mp.cosh(alpha * d) + mp.cos(mp.pi * alpha)))


print("=== A. representation K_a(e^{ax},e^{ay}) via J ===")
alpha = mp.mpf('0.45')
pts = [(mp.mpf('-1.2'), mp.mpf('0.4')), (mp.mpf('2.0'), mp.mpf('2.9')), (mp.mpf('-3.0'), mp.mpf('-0.5')), (mp.mpf('0'), mp.mpf('0'))]
for x, y in pts:
    lhs = K(alpha, mp.e ** (alpha * x), mp.e ** (alpha * y))
    Jv, tail = J_quad(x - y, alpha)
    rhs = mp.pi * mp.e ** ((1 - alpha) * (x + y)) / mp.sin(mp.pi * alpha) * mp.e ** (-(x + y)) * Jv
    print(f"x={float(x):5} y={float(y):5}: lhs={float(lhs):.12e} rhs={float(rhs):.12e} "
          f"relerr={float(abs(lhs-rhs)/abs(lhs)):.2e} tailbound={float(tail):.2e}", flush=True)

print()
print("=== B. discrete Andreief (Cauchy-Binet) ===")
rng = np.random.default_rng(3)
n, N = 4, 12
A = rng.normal(size=(n, N)); B = rng.normal(size=(n, N)); w = np.exp(rng.normal(size=N))
lhs = A @ np.diag(w) @ B.T
rhs = np.zeros((n, n))
for Ks in it.combinations(range(N), n):
    Kl = list(Ks)
    rhs += np.linalg.det(A[:, Kl]) * np.linalg.det(B[:, Kl]) * np.prod(w[Kl])
print("max|lhs-rhs| =", float(np.abs(lhs - rhs).max()), " scale:", float(np.abs(lhs).max()))
