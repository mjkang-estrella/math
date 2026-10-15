"""Round-2 supporting checks for the I345 repaired proof review.

Standard library only; run with `python3 -I r2_checks.py`.
Exact rational arithmetic is used for identities. Inequalities that are
proved analytically in review.md are additionally sampled in floating point;
sampling is evidence for transcription errors only, never a proof.
"""

import math
import random
from fractions import Fraction as Fr

random.seed(20261014)
FAIL = []


def check(name, cond):
    if not cond:
        FAIL.append(name)
        raise AssertionError(name)


def rq(lo=-5, hi=5, den=7):
    return Fr(random.randint(lo * den, hi * den), den)


# ---------------------------------------------------------------- linear algebra
def matvec(M, v):
    return [sum(M[i][j] * v[j] for j in range(len(v))) for i in range(len(M))]


def quad(M, v):
    return sum(v[i] * matvec(M, v)[i] for i in range(len(v)))


def trace_prod(A, B):
    n = len(A)
    return sum(A[i][j] * B[j][i] for i in range(n) for j in range(n))


def sym_rand(n):
    X = [[Fr(0)] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            X[i][j] = X[j][i] = rq()
    return X


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))]
            for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def is_pd_float(M, shift):
    """Cholesky test of M - shift*I > 0 (float)."""
    n = len(M)
    A = [[float(M[i][j]) - (shift if i == j else 0.0) for j in range(n)] for i in range(n)]
    L = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1):
            s = A[i][j] - sum(L[i][k] * L[j][k] for k in range(j))
            if i == j:
                if s <= 0:
                    return False
                L[i][i] = math.sqrt(s)
            else:
                L[i][j] = s / L[j][j]
    return True


# ===================================================== C1. R1 compact-p lemma
def c1_holder_8():
    """(8): |s x^s - s y^s| <= S max(1,S) (x+y)^(s-a) |x-y|^a."""
    worst = 0.0
    for m in range(3, 9):
        a = min(0.5, 1.0 / (m - 2))
        for S in (0.5, 1.0, 2.5, 10.0):
            K = S * max(1.0, S)
            for _ in range(3000):
                s = random.uniform(0.5, S)
                x = random.choice([0.0, random.random(), random.random() ** 8])
                y = random.choice([0.0, random.random(), x * (1 + 1e-6)])
                if x + y == 0:
                    continue
                lhs = abs(s * x ** s - s * y ** s)
                rhs = K * (x + y) ** (s - a) * abs(x - y) ** a
                worst = max(worst, lhs / rhs if rhs > 0 else (0 if lhs == 0 else math.inf))
    check("C1 (8) Holder structure constant", worst <= 1.0 + 1e-12)
    return worst


def F_s(v, s):
    r = math.sqrt(sum(c * c for c in v))
    return [r ** s * c for c in v]


def A_s(v, s):
    r = math.sqrt(sum(c * c for c in v))
    return [r ** (2 * s) * c for c in v]


def DA_s(w, s, h):
    r2 = sum(c * c for c in w)
    q = 2 * s
    dot = sum(a * b for a, b in zip(w, h))
    return [r2 ** (q / 2) * hi + q * r2 ** (q / 2 - 1) * dot * wi for hi, wi in zip(h, w)]


def rand_ball(m, rmin, rmax):
    while True:
        v = [random.gauss(0, 1) for _ in range(m)]
        n = math.sqrt(sum(c * c for c in v))
        if n > 0:
            r = random.uniform(rmin, rmax)
            return [c * r / n for c in v]


def c1_inverse_12_and_taylor_11():
    """(12) inverse comparison and the uniform Taylor remainder behind (11)."""
    worst12 = 0.0
    worst_mono = 0.0
    worst_tay = 0.0
    for m in (3, 4, 6):
        for S in (0.5, 1.5, 4.0):
            for _ in range(1500):
                s = random.uniform(0.5, S)
                w = rand_ball(m, 0.5, 1.0)
                v = rand_ball(m, 0.0, 1.0)
                d = math.sqrt(sum((a - b) ** 2 for a, b in zip(v, w)))
                if d == 0:
                    continue
                Fv, Fw = F_s(v, s), F_s(w, s)
                dF = math.sqrt(sum((a - b) ** 2 for a, b in zip(Fv, Fw)))
                worst12 = max(worst12, d / (2 ** (2 * S + 2) * dF))
                R = max(math.sqrt(sum(c * c for c in v)), math.sqrt(sum(c * c for c in w)))
                mono = sum((a - b) * (c - e) for a, b, c, e in zip(Fv, Fw, v, w))
                worst_mono = max(worst_mono, 2 ** (-S - 2) * R ** s * d * d / mono)
                Av, Aw = A_s(v, s), A_s(w, s)
                lin = DA_s(w, s, [a - b for a, b in zip(v, w)])
                rem = math.sqrt(sum((a - b - c) ** 2 for a, b, c in zip(Av, Aw, lin)))
                worst_tay = max(worst_tay, rem / d ** 2)
    check("C1 (12) inverse comparison", worst12 <= 1.0)
    check("C1 (12) monotonicity lower bound", worst_mono <= 1.0)
    # Bounded Taylor ratio over the compact family (C(m,P) finite): evidence only.
    check("C1 (11) Taylor remainder ratio bounded", worst_tay < 50.0)
    return worst12, worst_mono, worst_tay


def c1_iteration_15():
    """(14)-(15): contraction E_{i+1}<=(t/2)E_i and drift <= 1/8, worst case."""
    for m in range(3, 9):
        a = min(0.5, 1.0 / (m - 2))
        for C3 in (1.0, 3.0, 10.0, 1e3, 1e6):
            t = min(1 / 8, 1 / (4 * C3))
            eps = min(1.0, 1 / (256 * C3 ** 2), (t ** (m + 1) / (4 * C3)) ** (1 / a))
            E = eps
            drift = 0.0
            for _ in range(200):
                drift += C3 * math.sqrt(E)
                En = C3 * (t * t + t ** (-m) * E ** a) * E
                check("C1 (15) contraction", En <= (t / 2) * E * (1 + 1e-12))
                E = En
            check("C1 (15) drift <= 1/8", drift <= 0.125 + 1e-12)
            # reference norm budget: |omega_0|^2>=1/2 and drift 1/8 keep >=1/4
            check("C1 reference lower size", 0.5 - 2 * 0.125 >= 0.25 - 1e-15)
    return True


def c1_decay_17():
    """(16)-(17): common lambda_* satisfies both printed (5.4) inequalities."""
    for C5 in (1.0, 2.0, 50.0, 1e4):
        for S in (0.5, 1.0, 3.0, 20.0):
            for eps_star in (1e-1, 1e-4, 1e-9):
                lam = min(0.25, 1 / (16 * C5 ** 2), eps_star / (2 * C5 * 2 ** (S + 1)))
                for k in range(50):
                    s = 0.5 + (S - 0.5) * k / 49
                    check("C1 (16a)", 1 - C5 * math.sqrt(lam) >= 2 ** (-(s + 1) / 2))
                    check("C1 (16b)", lam * C5 * 2 ** (s + 1) <= eps_star * (1 + 1e-12))
                # log1p: lambda_* can be ~1e-20, where log(1-lam) rounds to 0.
                theta = -math.log1p(-lam) / (2 * math.log(4))
                check("C1 (5.5) theta", abs(0.5 * math.log1p(-lam) + theta * math.log(4)) < 1e-15
                      and 0 < theta < 0.5)
    return True


# ===================================================== C2. R2 Savin family
def M_coef(qx, qt, a, b, e, eps, A, d):
    """Coefficient matrix of F_d(X,q)=tr(M(q)X) in dimension N=len(a)+1 (float)."""
    n = len(a)
    N = n + 1
    v = [d * c for c in qx] + [1 + e * d * qt]
    B = 1 + eps * (2 * d * qt + d * d * sum(c * c for c in qx)) + eps * eps * A * d * d * qt * qt
    B = max(B, 0.0)
    xi = list(a) + [b]
    Pi = [[(1.0 if i == j else 0.0) - xi[i] * xi[j] for j in range(N)] for i in range(N)]
    S = [1.0] * n + [math.sqrt(e)]
    return [[v[i] * v[j] + B * S[i] * Pi[i][j] * S[j] for j in range(N)] for i in range(N)], B


def c2_ellipticity():
    worst_B = 1.0
    for n in (1, 2, 3, 4):
        for b0 in (0.1, 0.3, 0.7):
            rho = min(1 / 8, b0 * b0 / 30)
            for _ in range(400):
                b = random.uniform(b0, 1.0)
                av = rand_ball(n, 1.0, 1.0)
                alpha = math.sqrt(max(0.0, 1 - b * b))
                a = [alpha * c for c in av]
                e, eps, A, d = (random.choice([0.0, 1.0, random.random()]) for _ in range(4))
                # zero jet: [b0^2/3, 2]
                M0, _ = M_coef([0.0] * n, 0.0, a, b, e, eps, A, d)
                check("C2 M0 lower", is_pd_float(M0, b0 * b0 / 3 * (1 - 1e-9)))
                check("C2 M0 upper", is_pd_float([[2.0 * (i == j) - M0[i][j] for j in range(n + 1)]
                                                  for i in range(n + 1)], -1e-12))
                # common radius rho=min(1/8,b0^2/30): eigenvalues in [b0^2/6, 3]
                q = rand_ball(n + 1, 0.0, rho)
                M, B = M_coef(q[:n], q[n], a, b, e, eps, A, d)
                q8 = rand_ball(n + 1, 0.0, 1 / 8)
                _, B8 = M_coef(q8[:n], q8[n], a, b, e, eps, A, d)
                worst_B = min(worst_B, B8)
                check("C2 B_d>=3/4 on |q|<=1/8", B8 >= 0.75)
                check("C2 radius lower", is_pd_float(M, b0 * b0 / 6))
                check("C2 radius upper", is_pd_float([[3.0 * (i == j) - M[i][j] for j in range(n + 1)]
                                                      for i in range(n + 1)], 0.0))
    return worst_B


def c2_amplitude_exact():
    """F_1(D2W,DW) = d * F_d(D2Z,DZ) for W=dZ, exact rationals (e=t^2)."""
    for _ in range(200):
        n = random.randint(1, 3)
        N = n + 1
        t = Fr(random.randint(0, 7), 7)
        e = t * t
        eps, A = Fr(random.randint(0, 9), 9), Fr(random.randint(0, 9), 9)
        d = Fr(random.randint(1, 9), 9)
        a = [rq(-1, 1) for _ in range(n)]
        b = rq(-1, 1)  # unit normalisation is not needed for the identity
        xi = a + [b]
        Pi = [[(1 if i == j else 0) - xi[i] * xi[j] for j in range(N)] for i in range(N)]
        S = [Fr(1)] * n + [t]
        SPS = [[S[i] * Pi[i][j] * S[j] for j in range(N)] for i in range(N)]
        X = sym_rand(N)
        q = [rq() for _ in range(N)]

        def F(dd, XX, qq):
            v = [dd * c for c in qq[:n]] + [1 + e * dd * qq[n]]
            Bd = 1 + eps * (2 * dd * qq[n] + dd * dd * sum(c * c for c in qq[:n])) \
                + eps * eps * A * dd * dd * qq[n] ** 2
            return quad(XX, v), Bd, trace_prod(SPS, XX)

        rW, BW, tW = F(1, [[d * x for x in r] for r in X], [d * c for c in q])
        rZ, BZ, tZ = F(d, X, q)
        check("C2 amplitude rank-one", rW == d * rZ)
        check("C2 amplitude B", BW == BZ)
        check("C2 amplitude trace", tW == d * tZ)
    return True


# ===================================================== C3. I236 / appendix identities
def G_tau(tau, px, X, m):
    v = list(px) + [Fr(1)]
    return quad(X, v) + tau * sum(X[k][k] for k in range(m))


def c3_frame_and_reflection():
    for _ in range(300):
        m = random.randint(1, 3)
        N = m + 1
        tau = Fr(random.randint(1, 20), 5)
        R = Fr(random.randint(1, 20), 4)
        p0 = [rq() for _ in range(m)]
        Vx = [rq() for _ in range(m)]
        X = sym_rand(N)
        # U(y,s)=V(x0+R(y+p0 s),t0+Rs)/R - p0.y - (...)s ; Hessian R J^T X J
        J = [[Fr(1) if i == j else Fr(0) for j in range(m)] + [p0[i]] for i in range(m)] \
            + [[Fr(0)] * m + [Fr(1)]]
        HU = [[R * c for c in r] for r in matmul(transpose(J), matmul(X, J))]
        Ux = [Vx[i] - p0[i] for i in range(m)]
        check("C3 frame G_tau[U]=R G_tau[V]", G_tau(tau, Ux, HU, m) == R * G_tau(tau, Vx, X, m))
        # reflection Vt(x,t)=-V(x,-t): gradient (-Vx, Vt), Hessian -D X D
        D = [[Fr(1) if (i == j and i < m) else (Fr(-1) if i == j else Fr(0)) for j in range(N)]
             for i in range(N)]
        HR = [[-c for c in r] for r in matmul(D, matmul(X, D))]
        check("C3 reflection G -> -G", G_tau(tau, [-c for c in Vx], HR, m) == -G_tau(tau, Vx, X, m))
    return True


def c3_fit_transform():
    """Frame maps fit (p,a) to (p-p0,a-a0) with domain |k-(p-p0)sigma|<=rho."""
    for _ in range(300):
        m = random.randint(1, 3)
        p, p0 = [rq() for _ in range(m)], [rq() for _ in range(m)]
        a, a0 = rq(), rq()
        R = Fr(random.randint(1, 20), 3)
        k = [rq() for _ in range(m)]
        sig = rq()
        h = [R * (k[i] + p0[i] * sig) for i in range(m)]
        ell = R * sig
        dot = lambda u, w: sum(x * y for x, y in zip(u, w))
        lhs = (dot(p, h) + (a - dot(p, p) / 2) * ell) / R - dot(p0, k) - (a0 + dot(p0, p0) / 2) * sig
        pp = [p[i] - p0[i] for i in range(m)]
        rhs = dot(pp, k) + (a - a0 - dot(pp, pp) / 2) * sig
        check("C3 fit transform value", lhs == rhs)
        dom_V = [h[i] - p[i] * ell for i in range(m)]
        dom_U = [R * (k[i] - pp[i] * sig) for i in range(m)]
        check("C3 fit transform domain", dom_V == dom_U)
    return True


def c3_time_lipschitz_test():
    """G_tau of psi(T)+p.(Y-x0)+K'|Y-x0|^2/2 equals psi''+K'(|p+K'(y-x0)|^2+tau m)."""
    for _ in range(200):
        m = random.randint(1, 3)
        tau, Kp, psi2 = rq(0, 5), rq(0, 5), rq()
        p = [rq() for _ in range(m)]
        y = [rq() for _ in range(m)]
        grad = [p[i] + Kp * y[i] for i in range(m)]
        X = [[Kp if (i == j and i < m) else Fr(0) for j in range(m + 1)] for i in range(m + 1)]
        X[m][m] = psi2
        check("C3 Lemma 2.1 test", G_tau(tau, grad, X, m) ==
              psi2 + Kp * (sum(c * c for c in grad) + tau * m))
    return True


def c3_flux():
    """Da = exp(H/tau) A_tau / tau (finite differences) and the lambda_0 bound."""
    worst_fd = 0.0
    worst_l0 = 0.0
    for _ in range(300):
        m = random.randint(1, 3)
        tau = random.uniform(0.1, 5)
        P = [random.uniform(-1, 1) for _ in range(m + 1)]
        Mn = math.sqrt(sum(c * c for c in P))

        def a_flux(P):
            H = P[m] + sum(c * c for c in P[:m]) / 2
            return [math.exp(H / tau) * c for c in P[:m]] + [math.exp(H / tau)]

        H = P[m] + sum(c * c for c in P[:m]) / 2
        pref = math.exp(H / tau) / tau
        Atau = [[(tau if (i == j and i < m) else 0.0) + (P[i] if i < m else 1.0) * (P[j] if j < m else 1.0)
                 for j in range(m + 1)] for i in range(m + 1)]
        hstep = 1e-6
        for j in range(m + 1):
            Pp = list(P); Pp[j] += hstep
            Pm = list(P); Pm[j] -= hstep
            col = [(x - y) / (2 * hstep) for x, y in zip(a_flux(Pp), a_flux(Pm))]
            for i in range(m + 1):
                worst_fd = max(worst_fd, abs(col[i] - pref * Atau[i][j]) / (1 + abs(pref * Atau[i][j])))
        lam0 = 1 / max(2, (1 + 2 * Mn * Mn) / tau)
        for _ in range(20):
            z = rand_ball(m + 1, 1.0, 1.0)
            worst_l0 = max(worst_l0, lam0 * 1.0 / sum(z[i] * sum(Atau[i][j] * z[j] for j in range(m + 1))
                                                      for i in range(m + 1)))
    check("C3 flux derivative", worst_fd < 1e-6)
    check("C3 lambda_0 lower bound", worst_l0 <= 1 + 1e-12)
    return worst_fd, worst_l0


def c3_envelope_algebra():
    """Variance term affine along ((q_j),1); weighted mean of q_j; envelope scaling."""
    for _ in range(200):
        m = random.randint(1, 3)
        k = random.randint(2, 4)
        th = [Fr(random.randint(1, 9)) for _ in range(k)]
        tot = sum(th)
        th = [c / tot for c in th]
        ys = [[rq() for _ in range(m)] for _ in range(k)]
        xb = [sum(th[j] * ys[j][i] for j in range(k)) for i in range(m)]
        t = Fr(random.randint(1, 9), 3)
        Dphi = [rq() for _ in range(m)]
        qs = [[Dphi[i] + (ys[j][i] - xb[i]) / t for i in range(m)] for j in range(k)]
        check("C3 weighted mean of q_j", [sum(th[j] * qs[j][i] for j in range(k)) for i in range(m)] == Dphi)

        def var_term(hh):
            Y = [[ys[j][i] + hh * qs[j][i] for i in range(m)] for j in range(k)]
            xbh = [sum(th[j] * Y[j][i] for j in range(k)) for i in range(m)]
            return sum(th[j] * sum((Y[j][i] - xbh[i]) ** 2 for i in range(m)) for j in range(k)) / (2 * (t + hh))

        vals = [var_term(Fr(hh)) for hh in (0, 1, 2, 3)]
        check("C3 variance affine (2nd diff)", vals[2] - 2 * vals[1] + vals[0] == 0)
        check("C3 variance affine (3rd pt)", vals[3] - 2 * vals[2] + vals[1] == 0)
        # envelope scaling: one configuration of C_{s'}U at 0 for U(y)=V(Ry)/R
        R = Fr(random.randint(1, 9), 2)
        sp = Fr(random.randint(1, 9), 4)
        Vvals = [rq() for _ in range(k)]  # values V(R y_j)
        lhsU = sum(th[j] * Vvals[j] / R for j in range(k)) - sum(
            th[j] * sum(c * c for c in ys[j]) for j in range(k)) / (2 * sp)
        zs = [[R * c for c in y] for y in ys]
        rhsV = (sum(th[j] * Vvals[j] for j in range(k)) - sum(
            th[j] * sum(c * c for c in zs[j]) for j in range(k)) / (2 * sp * R)) / R
        check("C3 envelope parameter scaling", lhsU == rhsV)
    return True


# ===================================================== C4. coarse-cylinder lemma (R5)
def c4_coarse_geometry():
    for _ in range(300):
        H = Fr(random.randint(1, 50), 7)
        e = Fr(random.randint(1, 100), 100)
        eta = e * Fr(random.randint(1, 100), 100)  # eta <= e
        c = Fr(random.randint(50, 300), 100)
        r2 = eta / e  # (ell/(H/4))^2
        ell2 = (H / 4) ** 2 * r2
        # transverse half-width ell*sqrt(e) vs sqrt(eta)H/4 ; axial ell vs H/4
        check("C4 ellipsoid transverse", ell2 * e == eta * H * H / 16)
        check("C4 ellipsoid axial", ell2 <= H * H / 16)
        # ||W||: eta H/(c ell e) = (4/c) sqrt(eta/e)  (compare squares)
        check("C4 W bound", (eta * H / (c * e)) ** 2 / ell2 == (4 / c) ** 2 * r2)
        # (7.5): (c e/ell) * C*(4/c)sqrt(eta/e) = 16 C e/H  (compare squares, C=1)
        check("C4 Hessian scaling", (c * e) ** 2 / ell2 * (4 / c) ** 2 * r2 == (16 * e / H) ** 2)
    return True


# ===================================================== C5. strengthened selection (R4)
def c5_selection():
    """b(s)=1/(1+log(1/s)) has no power bound; log-space run of the R4 construction."""
    # f_i(sigma)=exp(sigma/i)/(1+sigma), sigma=log(1/s), s0=1/8
    s0 = math.log(8)
    out = []
    for i in range(2, 9):
        g = 1.0 / i
        lf = lambda sg: sg * g - math.log1p(sg)
        # find a_i: smallest sigma_max with sup_{s0<=sigma<=sigma_max} f_i > 2i
        sm = s0
        while max(lf(s0), lf(sm)) <= math.log(2 * i):
            sm += 0.5
        grid = [s0 + (sm - s0) * j / 4000 for j in range(4001)]
        Mi = max(lf(x) for x in grid)
        # choose s_i: smallest sigma (largest s) with f_i > M_i/2
        si = next(x for x in grid if lf(x) > Mi - math.log(2))
        check("C5 f_i(s_i)>i", lf(si) > math.log(i))
        check("C5 running max", all(lf(x) <= lf(si) + math.log(2) + 1e-12 for x in grid if x <= si))
        bsi = 1 / (1 + si)
        for kk in (1, 2, 3):
            # worst lambda = b/4: log(s_i/lambda^k) = -sigma_i - k log(b/4)
            val = -si - kk * math.log(bsi / 4)
            bound = kk * math.log(4 / i) + (1 - kk * g) * (-si)
            check("C5 scale separation bound", val < bound + 1e-9)
        out.append((i, round(si, 2)))
    return out


def main():
    print("PASS C1 (8) structure constant, worst ratio %.4f" % c1_holder_8())
    w12, wm, wt = c1_inverse_12_and_taylor_11()
    print("PASS C1 (12) inverse comparison worst %.4f, monotone worst %.4f; (11) Taylor sup ratio %.3f"
          % (w12, wm, wt))
    c1_iteration_15(); print("PASS C1 (14)-(15) contraction t/2 and drift <= 1/8, m=3..8, C3 up to 1e6")
    c1_decay_17(); print("PASS C1 (16)-(17) common lambda_* and theta in (0,1/2)")
    print("PASS C2 eigenvalues: M0 in [b0^2/3,2], |q|<=min(1/8,b0^2/30) in [b0^2/6,3]; min B_d %.4f"
          % c2_ellipticity())
    c2_amplitude_exact(); print("PASS C2 amplitude identity F_1(dZ) = d F_d(Z) (exact)")
    c3_frame_and_reflection(); print("PASS C3 frame G_tau[U]=R G_tau[V], reflection (exact)")
    c3_fit_transform(); print("PASS C3 fit transform (p,a)->(p-p0,a-a0) (exact)")
    c3_time_lipschitz_test(); print("PASS C3 Lemma 2.1 lifted-test identity (exact)")
    fd, l0 = c3_flux(); print("PASS C3 flux derivative (fd err %.1e), lambda_0 bound (worst %.4f)" % (fd, l0))
    c3_envelope_algebra(); print("PASS C3 variance affine, weighted mean, envelope scaling (exact)")
    c4_coarse_geometry(); print("PASS C4 coarse ellipsoid geometry and (7.2),(7.5) scaling (exact)")
    print("PASS C5 R4 selection on b=1/(1+log(1/s)); (i, log(1/s_i)):", c5_selection())
    print("ALL PASS" if not FAIL else "FAILURES: %s" % FAIL)


if __name__ == "__main__":
    main()
