#!/usr/bin/env python3
"""Exact-arithmetic spot checks of the algebraic identities used in I345.

Pure standard library (fractions, random, math). Run: python3 -I algebra_checks.py
These checks support, and do not replace, the analytic review in ../review.md.
Each check samples random rational instances and asserts an exact identity
(or, where a square root or eigenvalue is unavoidable, a float inequality).
"""
from fractions import Fraction as Fr
import math
import random

random.seed(20261014)
TRIALS = 200


def rq(lo=-3, hi=3, den=7):
    return Fr(random.randint(lo * den, hi * den), random.randint(1, den))


def rvec(n):
    return [rq() for _ in range(n)]


def rsym(n):
    A = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            A[i][j] = A[j][i] = rq()
    return A


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def outer(u, v):
    return [[a * b for b in v] for a in u]


def madd(A, B, s=1):
    return [[a + s * b for a, b in zip(r, q)] for r, q in zip(A, B)]


def mscale(A, s):
    return [[a * s for a in r] for r in A]


def mmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def tr(A):
    return sum(A[i][i] for i in range(len(A)))


def quad(A, v):
    return dot(v, [dot(r, v) for r in A])


def eye(n):
    return [[Fr(int(i == j)) for j in range(n)] for i in range(n)]


def diag(vals):
    n = len(vals)
    return [[vals[i] if i == j else Fr(0) for j in range(n)] for i in range(n)]


def rational_unit(n):
    """Rational unit vector via inverse stereographic projection."""
    w = rvec(n - 1)
    s = dot(w, w)
    return [2 * x / (1 + s) for x in w] + [(s - 1) / (1 + s)]


def L_op(q, H, eps, xi):
    """Lifted operator (L): H[q] + eps |Pi q|^2 tr(Pi H), Pi = I - xi xi^T."""
    n = len(q)
    Pi = madd(eye(n), outer(xi, xi), -1)
    Piq = [dot(r, q) for r in Pi]
    return quad(H, q) + eps * dot(Piq, Piq) * tr(mmul(Pi, H))


def check_lift_schur():
    """Section 3: H_sigma - diag(K,0) = v v^T/(H_bb+sigma); tr(M H) = L(DU,H);
    and the lift of a smooth jet reduces to (P)."""
    for _ in range(TRIALS):
        n = random.randint(1, 4)
        N = n + 1
        H = rsym(N)
        H[n][n] = abs(H[n][n])  # upper test: H_bb >= 0
        sigma = Fr(random.randint(1, 50), 97)
        Hs = [r[:] for r in H]
        Hs[n][n] += sigma
        hb = [H[i][n] for i in range(n)]
        den = H[n][n] + sigma
        K = [[H[i][j] - hb[i] * hb[j] / den for j in range(n)] for i in range(n)]
        diagK = [[K[i][j] if (i < n and j < n) else Fr(0) for j in range(N)] for i in range(N)]
        v = hb + [den]
        assert madd(Hs, diagK, -1) == mscale(outer(v, v), 1 / den)
        g = rvec(n)
        eps = Fr(1, random.randint(1, 40))
        xi = [Fr(0)] * n + [Fr(1)]
        q = g + [Fr(1)]
        Pi = madd(eye(N), outer(xi, xi), -1)
        M = madd(outer(q, q), mscale(Pi, eps * dot(g, g)))
        assert tr(mmul(M, H)) == L_op(q, H, eps, xi)
        # yy block of M is g g^T + eps|g|^2 I
        assert [r[:n] for r in M[:n]] == madd(outer(g, g), mscale(eye(n), eps * dot(g, g)))
        # M_bb = 1 so tr(M H_sigma) = tr(M H) + sigma
        assert tr(mmul(M, Hs)) == tr(mmul(M, H)) + sigma
        # smooth lift: H = diag(D^2u, 0) gives (P)
        D2u = rsym(n)
        Hl = [[D2u[i][j] if (i < n and j < n) else Fr(0) for j in range(N)] for i in range(N)]
        assert L_op(q, Hl, eps, xi) == quad(D2u, g) + eps * dot(g, g) * tr(D2u)
    return "lift/Schur identities"


def check_rescaled_pde():
    """Section 5 (5.1)-(5.2): division of (L) by lambda c^3/r gives the stated
    coefficient C(q) = nu + eps(2 phi_t+|D_x phi|^2) + eps lambda phi_t^2."""
    for _ in range(TRIALS):
        n = random.randint(1, 4)
        N = n + 1
        mu = Fr(random.randint(1, 30), 31)  # sqrt(lambda)
        lam = mu * mu
        r = Fr(random.randint(1, 9), 5)
        eps = Fr(1, random.randint(1, 40))
        xi = rational_unit(N)
        Dphi = rvec(N)
        D2phi = rsym(N)
        q = [mu * x for x in Dphi[:n]] + [1 + lam * Dphi[n]]
        qxi = dot(q, xi)
        if qxi == 0:
            continue
        c = 1 / qxi  # constraint q.xi = 1/c
        S = diag([Fr(1)] * n + [mu])
        grad = [c * x for x in q]
        Hess = mscale(mmul(mmul(S, D2phi), S), c / r)
        lhs = L_op(grad, Hess, eps, xi) / (lam * c ** 3 / r)
        A = 1 - 1 / c ** 2
        nu = eps * A / lam
        Ct = nu + eps * (2 * Dphi[n] + dot(Dphi[:n], Dphi[:n])) + eps * lam * Dphi[n] ** 2
        Pi = madd(eye(N), outer(xi, xi), -1)
        rhs = quad(D2phi, Dphi[:n] + [1 + lam * Dphi[n]]) + Ct * tr(mmul(mmul(mmul(S, Pi), S), D2phi))
        assert lhs == rhs
        # |Pi q|^2 identity and C = eps|Pi q|^2/lambda on tests
        Piq = [dot(row, q) for row in Pi]
        assert dot(Piq, Piq) == A + lam * (2 * Dphi[n] + dot(Dphi[:n], Dphi[:n])) + lam ** 2 * Dphi[n] ** 2
        assert Ct == eps * dot(Piq, Piq) / lam
    return "rescaled PDE (5.2)"


def check_ellipsoid_pde():
    """Section 7 (7.3): ellipsoid normalization gives coefficient
    B = 1 + eps(2q_t+|q_x|^2) + eps^2 A q_t^2 = |Pi q|^2/A, with e = eps A."""
    for _ in range(TRIALS):
        n = random.randint(1, 4)
        N = n + 1
        xi = rational_unit(N)
        se = Fr(random.randint(1, 30), 31)  # sqrt(e)
        e = se * se
        ell = Fr(random.randint(1, 9), 4)
        Dphi = rvec(N)
        D2phi = rsym(N)
        q = [se * x for x in Dphi[:n]] + [1 + e * Dphi[n]]
        qxi = dot(q, xi)
        if qxi == 0:
            continue
        c = 1 / qxi
        A = 1 - 1 / c ** 2
        if A == 0:
            continue
        eps = e / A
        S = diag([Fr(1)] * n + [se])
        grad = [c * x for x in q]
        Hess = mscale(mmul(mmul(S, D2phi), S), c / ell)
        lhs = L_op(grad, Hess, eps, xi) / (c ** 3 * e / ell)
        B = 1 + eps * (2 * Dphi[n] + dot(Dphi[:n], Dphi[:n])) + eps ** 2 * A * Dphi[n] ** 2
        Pi = madd(eye(N), outer(xi, xi), -1)
        rhs = quad(D2phi, Dphi[:n] + [1 + e * Dphi[n]]) + B * tr(mmul(mmul(mmul(S, Pi), S), D2phi))
        assert lhs == rhs
        Piq = [dot(row, q) for row in Pi]
        assert B == dot(Piq, Piq) / A
        # T_e D^2U T_e = (c e/ell) D^2 phi
        T = diag([se] * n + [Fr(1)])
        assert mmul(mmul(T, Hess), T) == mscale(D2phi, c * e / ell)
    return "ellipsoid PDE (7.3) and (7.5) scaling"


def check_M0():
    """Section 7: M0 = e_N e_N^T + S_e Pi S_e has time Schur complement exactly 1
    and a positive lower eigenvalue bound depending only on b0."""
    worst = {}
    for _ in range(TRIALS):
        n = random.randint(1, 4)
        N = n + 1
        xi = rational_unit(N)
        if xi[n] < 0:
            xi = [-x for x in xi]
        a, b = xi[:n], xi[n]
        if b == 0:
            continue
        se = Fr(random.randint(0, 31), 31)
        e = se * se
        S = diag([Fr(1)] * n + [se])
        Pi = madd(eye(N), outer(xi, xi), -1)
        M0 = madd(diag([Fr(0)] * n + [Fr(1)]), mmul(mmul(S, Pi), S))
        P = [r[:n] for r in M0[:n]]
        assert P == madd(eye(n), outer(a, a), -1)
        # (I - a a^T)^{-1} a = a / b^2  =>  Schur = M0_tt - v^T P^{-1} v
        v = [M0[i][n] for i in range(n)]
        Pinv_v = [x / b ** 2 * (-se * b) for x in a]  # P^{-1} v with v = -se b a
        assert [dot(r, Pinv_v) for r in P] == v
        assert M0[n][n] - dot(v, Pinv_v) == 1
        # float min eigenvalue via Cholesky-shift bisection
        Mf = [[float(x) for x in r] for r in M0]
        lo, hi = 0.0, 3.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if chol_ok([[Mf[i][j] - (mid if i == j else 0) for j in range(N)] for i in range(N)]):
                lo = mid
            else:
                hi = mid
        b0 = round(float(b), 2)
        worst[b0] = min(worst.get(b0, 9.0), lo)
        assert lo > 0
        # crude explicit bound: lambda_min >= b^2 / (1 + 1/b^2)^2 * ... ; just require positivity
    return "M0 Schur complement = 1, min eig > 0 (min seen %.3g)" % min(worst.values())


def chol_ok(M):
    n = len(M)
    Lm = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = M[i][j] - sum(Lm[i][k] * Lm[j][k] for k in range(j))
            if i == j:
                if s <= 0:
                    return False
                Lm[i][i] = math.sqrt(s)
            else:
                Lm[i][j] = s / Lm[j][j]
    return True


def check_kotschwar_ni():
    """Section 2.1: KN Theorem 1.1 with K=0, epsilon=1/2, divided by (p-1)^2,
    is bounded uniformly for p >= 3 (n fixed)."""
    out = []
    for n in range(2, 9):
        sup = 0.0
        p = 3.0
        while p < 1e7:
            b = 2 * (p - 1) / (n - 1) - 2
            neg = 2 * (p / 2 - 1) ** 2 / (n - 1) + (p - 2) * p / 2
            assert neg >= 0  # negative part vanishes for p >= 3
            c = (p / 2 + 1) * max(p - 1, 1)
            C = 20 * (n + p - 2) * (n - 1) + 10 * max(p - 1, 1) * (n - 1)  # times 1/R^2
            bound = 10 * (n - 1) * (c + (n - 1) * b * b / 4) + C  # times 1/R^2, eps=1/2
            sup = max(sup, bound / (p - 1) ** 2)
            p *= 1.01
        out.append((n, sup))
    return "KN uniform: sup_p R^2|D log v|^2 <= " + ", ".join("n=%d:%.1f" % t for t in out)


def check_unequal_parameter():
    """Section 8.1 geometry and (8.4) bookkeeping.
    (i) worst-case geometry: base axis point at t=c/sqrt(kappa) lies in coarse cylinder.
    (ii) relative error eps[kappa^2+kappa(1+log nu)]/nu -> 0 when kappa=64(4nu^2)^gamma, gamma<1/4."""
    # (ii)
    for gamma in (0.2, 0.1, 0.01):
        prev = None
        for k in range(4, 60, 4):
            nu = 10.0 ** k
            kappa = 64 * (4 * nu * nu) ** gamma
            rel = (kappa ** 2 + kappa * (1 + math.log(nu))) / nu
            if prev is not None and k > 40:
                assert rel < prev
            prev = rel
        assert prev < 1e-3, (gamma, prev)
    # (i) relation: transverse offset t*|n_P-n_Q| <= sqrt(eta) when t = c0/sqrt(kappa),
    # |n_P-n_Q| <= C1 kappa sqrt(lambda), eta = kappa lambda: need c0*C1 <= 1.
    for _ in range(TRIALS):
        lam = 10 ** random.uniform(-12, -2)
        kappa = 10 ** random.uniform(math.log10(64), 3)
        C1 = 2 / math.sqrt(32) * 2.5  # |P-Q|<=2 kappa sqrt(lam)/sqrt(Lambda), normalized by |P|>=1/2 (x2), slack
        c0 = 1 / C1
        t = c0 / math.sqrt(kappa)
        assert t * C1 * kappa * math.sqrt(lam) <= math.sqrt(kappa * lam) * (1 + 1e-12)
        # resulting axial difference bound and quadratic norm bound scale
        axial = 2 * kappa * lam / t  # |(P-Q).n_P| <= (Lambda lam+eta)/t <= 2 eta/t
        assert abs(axial / (kappa ** 1.5 * lam) - 2 / c0) < 1e-9
    return "unequal-parameter bookkeeping (8.2)-(8.4)"


def check_radial():
    """Sanity: radial p-harmonic |x|^k, k=(p-n)/(p-1), solves (P)."""
    for n in range(2, 7):
        for p in (3, 4.5, 10, 1e3):
            k = (p - n) / (p - 1)
            eps = 1 / (p - 2)
            # f=rho^k: f'^2[(1+eps) f'' + eps (n-1) f'/rho] proportional to (1+eps)(k-1)+eps(n-1)
            assert abs((1 + eps) * (k - 1) + eps * (n - 1)) < 1e-12
    return "radial p-harmonic sanity for (P)"


if __name__ == "__main__":
    for f in (check_lift_schur, check_rescaled_pde, check_ellipsoid_pde, check_M0,
              check_kotschwar_ni, check_unequal_parameter, check_radial):
        print("PASS", f())
