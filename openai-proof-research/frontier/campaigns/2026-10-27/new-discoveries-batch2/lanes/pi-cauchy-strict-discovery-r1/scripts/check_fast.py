"""Verification v5 — fast, decisive diagnostics only.

A. Integral representation: int_R f(e^{x-u}) f(e^{y-u}) e^{-2u} du == e^{-(x+y)} J(x-y),
   with J computed by 1D quadrature (v-substitution) and compared to
   sin(pa)/(2pi(cosh(a(x-y))+cos(pa))); then algebra gives K_a(e^{ax},e^{ay}).
B. Discrete Andreief/Cauchy-Binet identity (random complex-ish test).
C. D_x nonvanishing asymptotics ratio -> 1.
D. High-precision worst-minor scan strictly inside alpha<1/n.
"""
import mpmath as mp
import numpy as np
import itertools
from falpha import falpha, K

mp.mp.dps = 30


def ck(k, alpha):
    return (-1) ** (k + 1) * mp.gamma(1 + alpha * k) * mp.sin(mp.pi * alpha * k) / (mp.pi * mp.factorial(k))


def fser(z, alpha, KMAX=600):
    z = mp.mpf(z); alpha = mp.mpf(alpha)
    return mp.fsum([ck(k, alpha) * z ** (-alpha * k - 1) for k in range(1, KMAX + 1)])


def J_quad(d, alpha):
    d = mp.mpf(d); alpha = mp.mpf(alpha)
    g = lambda v: v * fser(mp.e ** (d / 2) * v, alpha) * fser(mp.e ** (-d / 2) * v, alpha)
    return mp.quad(g, ['1e-4', '0.01', '0.1', '1', '10', '100', '1e5'])


def J_closed(d, alpha):
    d = mp.mpf(d); alpha = mp.mpf(alpha)
    return mp.sin(mp.pi * alpha) / (2 * mp.pi * (mp.cosh(alpha * d) + mp.cos(mp.pi * alpha)))


print("=== A. representation K_a(e^{ax},e^{ay}) via J ===")
alpha = mp.mpf('0.45')
pts = [(mp.mpf('-1.2'), mp.mpf('0.4')), (mp.mpf('2.0'), mp.mpf('2.9')), (mp.mpf('-3.0'), mp.mpf('-0.5'))]
for x, y in pts:
    lhs = K(alpha, mp.e ** (alpha * x), mp.e ** (alpha * y))
    rhs = mp.pi * mp.e ** ((1 - alpha) * (x + y)) / mp.sin(mp.pi * alpha) * mp.e ** (-(x + y)) * J_quad(x - y, alpha)
    print(f"x={float(x):5} y={float(y):5}: lhs={float(lhs):.12e} rhs={float(rhs):.12e} relerr={float(abs(lhs-rhs)/abs(lhs)):.2e}", flush=True)

print()
print("=== B. discrete Andreief (Cauchy-Binet gram form) ===")
rng = np.random.default_rng(3)
n, N = 4, 12
A = rng.normal(size=(n, N)); B = rng.normal(size=(n, N)); w = np.exp(rng.normal(size=N))
lhs = A @ np.diag(w) @ B.T
rhs = np.zeros((n, n))
import itertools as it
for Kset in it.combinations(range(N), n):
    Ks = list(Kset)
    rhs += np.outer(np.linalg.det(A[:, Ks]), np.linalg.det(B[:, Ks])) * np.prod(w[Ks])
print("max |lhs-rhs| =", float(np.abs(lhs - rhs).max()))

print()
print("=== C. D_x nonvanishing asymptotics ===")
for n, alpha in [(2, '0.45'), (3, '0.3'), (4, '0.2'), (5, '0.15'), (6, '0.15')]:
    a = mp.mpf(alpha)
    xs = [mp.mpf('0.2') * (i + 1) ** 2 for i in range(n)]
    vs = [mp.mpf(i) * mp.mpf('0.7') for i in range(n)]
    z = [mp.e ** (-x) for x in xs]; w = [mp.e ** (v) for v in vs]
    Rdet = mp.det(mp.matrix([[z[i] ** (a * (j + 1) + 1) for j in range(n)] for i in range(n)]))
    Cdet = mp.det(mp.matrix([[w[i] ** (a * (j + 1) + 1) for j in range(n)] for i in range(n)]))
    lead = Rdet * Cdet
    for k in range(1, n + 1):
        lead *= ck(k, a)
    out = [f"n={n} a={alpha} lead={float(lead):.4e} nonzero={abs(lead)>1e-300}"]
    for U in [-15, -25, -35]:
        Dm = mp.matrix([[fser(mp.e ** (xs[i] - (mp.mpf(U) + vs[j])), a) for j in range(n)] for i in range(n)])
        detA = mp.det(Dm)
        ratio = detA / (lead * mp.e ** ((n + a * n * (n + 1) / 2) * mp.mpf(U)))
        out.append(f"U={U}: ratio={float(ratio):.8f}")
    print("  ".join(out), flush=True)

print()
print("=== D. high-precision worst-minor scan, strictly inside alpha<1/n ===")
def worst_minor_hp(n, alpha, trials, dps=60):
    mp.mp.dps = dps
    rng = np.random.default_rng(11)
    worst = mp.inf
    for _ in range(trials):
        m = int(rng.integers(2, n + 1))
        t = sorted([mp.e ** mp.mpf(rng.uniform(-9, 9)) for _ in range(m)])
        s = sorted([mp.e ** mp.mpf(rng.uniform(-9, 9)) for _ in range(m)])
        a = mp.mpf(alpha)
        A = mp.matrix(m, m)
        for i in range(m):
            for j in range(m):
                A[i, j] = K(a, t[i], s[j])
        for r in range(1, m + 1):
            for ri in itertools.combinations(range(m), r):
                for cj in itertools.combinations(range(m), r):
                    B = mp.matrix(r, r)
                    for ii, i in enumerate(ri):
                        for jj, j in enumerate(cj):
                            B[ii, jj] = A[i, j]
                    worst = min(worst, mp.det(B))
    mp.mp.dps = 30
    return worst

for n in [2, 3, 4, 5, 6, 7]:
    alpha = mp.mpf(1) / n - mp.mpf('0.01')
    w = worst_minor_hp(n, alpha, 40)
    print(f"n={n} alpha={float(alpha):.4f} (<1/n) worst minor (hp, 40 tuples) = {float(w):.4e}", flush=True)
# adversarial: nearly equal points
def worst_near(n, alpha, eps=1e-6):
    mp.mp.dps = 60
    a = mp.mpf(alpha)
    worst = mp.inf
    rng = np.random.default_rng(5)
    for _ in range(20):
        m = int(rng.integers(2, n + 1))
        base = [mp.e ** mp.mpf(rng.uniform(-5, 5))]
        for i in range(1, m):
            base.append(base[-1] * (1 + mp.mpf(eps)))
        t = base
        s = sorted([b * mp.e ** mp.mpf(rng.uniform(0.1, 3)) for b in base])
        A = mp.matrix(m, m)
        for i in range(m):
            for j in range(m):
                A[i, j] = K(a, t[i], s[j])
        for r in range(1, m + 1):
            for ri in itertools.combinations(range(m), r):
                for cj in itertools.combinations(range(m), r):
                    B = mp.matrix(r, r)
                    for ii, i in enumerate(ri):
                        for jj, j in enumerate(cj):
                            B[ii, jj] = A[i, j]
                    worst = min(worst, mp.det(B))
    mp.mp.dps = 30
    return worst

for n in [3, 5]:
    alpha = mp.mpf(1) / n - mp.mpf('0.005')
    print(f"n={n} alpha={float(alpha):.4f} worst near-equal minor = {float(worst_near(n, alpha)):.4e}", flush=True)
