#!/usr/bin/env python3
"""
Independent diagnostic checker for the preliminary review of
root-cauchy-strict-r1 (frozen @ review-freeze.json, 2026-10-28).

Solo review lane. Diagnostics only, never proof.

Checks:
  A  Zolotarev/Sato series (Theorem B) vs closed form at alpha=1/2  [series sanity]
  B  Lemma 3.1 Fourier side: inverse FT of sinh(pi xi)/(alpha sinh(pi xi/alpha))
     vs closed form J_alpha(d) = sin(pi alpha)/(2 pi (cosh(alpha d)+cos(pi alpha)))
  C  Lemma 3.2 prefactor: candidate's extra factor m in the exponent is WRONG
     (exact check against the Cauchy double-alternant at alpha=1/2, m=2)
  D  Lemma 5.1 asymptotics: corrected Vandermonde factor prod z_i^(1+alpha)
     (candidate's displayed identity is off by exactly prod z_i^alpha);
     includes a NEGATIVE x_i to exercise the false |r_k(i)|<=C claim
  E  Direct falsifier scan: all minors of K_alpha strictly positive for
     alpha<1/n (random + adversarial tuples); negative minors appear only
     for alpha>1/n, consistent with the source classification
  F  Generic-shortcut counterexample: f=e^{-|x|} is PF_infty with nonvanishing
     Fourier transform, yet f(x-y) has an exactly ZERO 2x2 minor
     ==> no generic "PF + nonvanishing FT => strict" theorem exists
"""
from mpmath import mp, mpf, exp, log, pi, sin, cos, sinh, cosh, gamma, quad, det, matrix, sqrt

mp.dps = 40

# ---------- f_alpha via the Zolotarev/Sato series (Theorem B) ----------
def c_k(k, a):
    return (-1)**(k+1) * gamma(1 + a*k) * sin(pi*a*k) / (pi * gamma(k+1))

def f_series(z, a, K=400):
    # sum_{k>=1} c_k z^{-alpha k - 1}; converges for all z>0, 0<a<1
    s = mpf(0)
    zk = z ** (-a - 1)          # k=1 term z^{-a-1}
    zz = z ** (-a)
    for k in range(1, K+1):
        s += c_k(k, a) * zk
        zk *= zz * (z ** 0)     # multiply by z^{-a} each step
        zk = z ** (-(a*(k+1)+1)) if k % 20 == 0 else zk  # periodic refresh
    return s

def f_half(z):  # closed form alpha = 1/2
    return z**(-mpf(3)/2) * exp(-mpf(1)/(4*z)) / (2*sqrt(pi))

# ---------- A: series vs closed form ----------
print("=== A: Zolotarev series sanity (alpha=1/2) ===")
for z in [mpf("0.7"), mpf(3), mpf(30), mpf(300)]:
    rel = abs(f_series(z, mpf(1)/2) - f_half(z)) / abs(f_half(z))
    print(f"  z={z}: relerr={float(rel):.2e}")

# ---------- B: Lemma 3.1 Fourier identification ----------
print("=== B: J_alpha closed form vs inverse Fourier transform ===")
def J_closed(d, a):
    return sin(pi*a) / (2*pi*(cosh(a*d) + cos(pi*a)))
def J_ft(d, a, Omega=160):
    g = lambda xi: cos(xi*d) * sinh(pi*xi) / (a * sinh(pi*xi/a))
    # split for quad accuracy; tail decays like exp(-(1/a-1)*pi*xi)
    return (1/pi) * quad(g, [0, 1, 5, 20, 60, Omega])
for a in [mpf("0.3"), mpf("0.55"), mpf("0.7")]:
    for d in [mpf("0.5"), mpf(2)]:
        L, R = J_ft(d, a), J_closed(d, a)
        print(f"  a={a} d={d}: FT={float(L):.10f} closed={float(R):.10f} relerr={float(abs(L-R)/abs(R)):.2e}")

# ---------- C: Lemma 3.2 prefactor bug (exact algebra check at alpha=1/2) ----------
print("=== C: Lemma 3.2 prefactor: candidate (extra m) vs corrected (no m) ===")
# alpha = 1/2: K_{1/2}(t,s) = 1/(t^2+s^2); det is the Cauchy double alternant (source Prop 1).
# corrected : det = (pi/sin(pa))^m e^{(1-a)(sum x + sum y)} (1/m!) int D_x D_y prod e^{-2u}
# candidate : same with e^{(1-a)*m*(sum x + sum y)}
a = mpf(1)/2
m = 2
x = [mpf("0.3"), mpf("1.7")]
y = [mpf("0.5"), mpf("2.2")]
t = [exp(xi/2) for xi in x]   # t_i = e^{alpha x_i}, alpha=1/2
s = [exp(yj/2) for yj in y]
Kmat = matrix([[1/(t[i]**2 + s[j]**2) for j in range(m)] for i in range(m)])
det_exact = det(Kmat)
# closed Cauchy double alternant: prod (s_j^2-s_i^2)(t_j^2-t_i^2) / prod (t_i^2+s_j^2)
det_cauchy = ((s[1]**2-s[0]**2)*(t[1]**2-t[0]**2)) / (
    (t[0]**2+s[0]**2)*(t[0]**2+s[1]**2)*(t[1]**2+s[0]**2)*(t[1]**2+s[1]**2))
print(f"  det[K] matrix vs Cauchy formula: {float(abs(det_exact-det_cauchy)):.2e} (exact identity)")

def D_f(v, xs):
    # det[ f(e^{x_i - v_j}) ], f = f_{1/2} closed form
    return det(matrix([[f_half(exp(xs[i]-v[j])) for j in range(len(xs))] for i in range(len(xs))]))

def gram_integral(xs, ys, A1=mpf(40), A2=mpf(14)):
    inner = lambda u2, u1: D_f([u1,u2], xs) * D_f([u1,u2], ys) * exp(-2*u1-2*u2)
    return quad(lambda u1: quad(lambda u2: inner(u2,u1), [-A1, -5, 0, A2]), [-A1, -5, 0, A2])

I = gram_integral(x, y)
P_fixed = (pi/sin(pi*a))**m * exp((1-a)*(sum(x)+sum(y)))       # corrected
P_m     = (pi/sin(pi*a))**m * exp((1-a)*m*(sum(x)+sum(y)))     # candidate (extra m)
lhs = (1/mpf(m)) * I
print(f"  (1/m!)int D_x D_y e^-2u du = {float(lhs):.8f}")
print(f"  det[K] exact              = {float(det_exact):.8f}")
print(f"  corrected prefactor ratio = {float(det_exact/(P_fixed*lhs)):.12f}   (should be 1)")
print(f"  candidate  prefactor ratio= {float(det_exact/(P_m*lhs)):.12f}   (should NOT be 1; = e^(-(1-a)(m-1)(sum x+sum y)))")
print(f"  predicted off-factor      = {float(exp((1-a)*(m-1)*(sum(x)+sum(y))))}")

# ---------- D: Lemma 5.1 asymptotics with corrected Vandermonde factor ----------
print("=== D: Lemma 5.1 leading-layer asymptotics (with negative x_1) ===")
def D_x_U(U, xs, a, m, K=250):
    # D_x(U+v_1..U+v_m) with v_j = j; direct series evaluation
    M = matrix([[f_series(exp(xs[i] - U - j), a, K) for j in range(1, m+1)] for i in range(len(xs))])
    return det(M)
def leading_corrected(xs, a, m):
    z = [exp(-xi) for xi in xs]
    w = [exp(j) for j in range(1, m+1)]
    Vz = mpf(1)
    zz = [zi**a for zi in z]
    for i in range(m):
        for j in range(i+1, m):
            Vz *= zz[j]-zz[i]
    Vw = mpf(1)
    ww = [wj**a for wj in w]
    for i in range(m):
        for j in range(i+1, m):
            Vw *= ww[j]-ww[i]
    Dz = mpf(1)
    for zi in z: Dz *= zi**(1+a)
    Dz *= Vz
    Dw = mpf(1)
    for wj in w: Dw *= wj**(1+a)
    Dw *= Vw
    ck = mpf(1)
    for k in range(1, m+1): ck *= c_k(k, a)
    return ck * Dz * Dw
for (m, a) in [(3, mpf("0.3")), (4, mpf("0.2"))]:
    xs = [-mpf("0.7"), mpf("0.3"), mpf("1.1")] + ([mpf("2.3")] if m == 4 else [])
    L = leading_corrected(xs, a, m)
    print(f"  (m,alpha)=({m},{a}), x={xs}")
    for U in [-15, -25, -35]:
        ratio = D_x_U(mpf(U), xs, a, m) / (L * exp((m + a*m*(m+1)/2)*U))
        # candidate's version: missing prod z_i^alpha
        prodz = mpf(1)
        for xi in xs: prodz *= exp(-xi*a)
        ratio_cand = ratio * prodz   # if candidate's L were used, ratio -> prod z_i^alpha
        print(f"    U={U}: corrected ratio={float(ratio):.6f}  candidate-version ratio={float(ratio_cand):.6f}")

# ---------- E: direct falsifier scan of minors of K_alpha ----------
print("=== E: strict positivity scan of all minors (falsifier hunt) ===")
import random
random.seed(20261028)
def K_entry(ti, sj, a):
    return 1/(ti*ti + 2*cos(pi*a)*ti*sj + sj*sj)
def det_minor(ts, ss, a):
    return det(matrix([[K_entry(ti, sj, a) for sj in ss] for ti in ts]))
def scan(n, a, trials=40, label=""):
    worst = mpf(10)
    for _ in range(trials):
        mm = random.randint(2, n)
        xs = sorted(random.uniform(-6, 6) for _ in range(mm))
        ys = sorted(random.uniform(-6, 6) for _ in range(mm))
        if random.random() < 0.5:  # adversarial near-equal
            xs = [xi*0.01 + 0.5*i for i, xi in enumerate(xs)]
            ys = [yi*0.01 + 0.5*i for i, yi in enumerate(ys)]
        ts = [exp(a*xi) for xi in xs]; ss = [exp(a*yj) for yj in ys]
        d = det_minor(ts, ss, a)
        if d < worst: worst = d
    return worst
for n, alphas in [(6, ["0.05", "0.1", "0.15"]), (3, ["0.2", "0.3"])]:
    for astr in alphas:
        w = scan(n, mpf(astr))
        print(f"  n={n} alpha={astr} (<1/{n}): min minor over 40 trials = {float(w):.3e}  [{'ALL>0' if w>0 else 'ZERO/NEG FOUND'}]")
# consistency: above the threshold negatives must appear
for n, astr in [(2, "0.6"), (3, "0.4")]:
    found = False
    for _ in range(400):
        mm = n
        xs = sorted(random.uniform(-6, 6) for _ in range(mm))
        ys = sorted(random.uniform(-6, 6) for _ in range(mm))
        ts = [exp(mpf(astr)*xi) for xi in xs]; ss = [exp(mpf(astr)*yj) for yj in ys]
        if det_minor(ts, ss, mpf(astr)) < 0:
            found = True; break
    print(f"  n={n} alpha={astr} (>1/{n}): negative {n}x{n} minor found: {found} (consistency with source Theorem (b))")

# ---------- F: generic-shortcut counterexample ----------
print("=== F: e^{-|x|} in PF_infty with fhat != 0, yet kernel e^{-|x-y|} NOT strict ===")
print("  x1-y1=5, x1-y2=4, x2-y2=5, x2-y1=6 (consistent with x1<x2, y1<y2):")
print("  det = e^{-5}e^{-5} - e^{-4}e^{-6} =", float(exp(-10) - exp(-4-6)))
print("  (exact zero: e^{-10}=e^{-10}). fhat(e^{-|x|}) = 2/(1+xi^2) != 0 everywhere.")
print("DONE")
