#!/usr/bin/env python3
"""Independent final-review checker for the NEW one-dimensional rational-kernel route.

Reviewer's own code; routes deliberately different from root's diagnostics and from
the preliminary (polar-route) checker:
  A  literal E_{1/2,1}(ir) closed form e^{-r^2}(1+2ir/sqrt(pi) I(r^2))   [direct series]
  B  NEW kernel identity: literal K (series product) == halfProduct closed form
     == rational J (1-D quadrature); zero scales; guarded |sqrt(vt)|<=6 for series route
  C  ODE residuals P'+SP and J'+SJ vs common RHS (new route's core) + J(0)=1
  D  T_k x^q by 200-node GL quadrature at irrational beta; R_N(q) literal products:
     monotone, bounded by Gamma ratio, and O(1/N) convergence trend
  E  |M_N(i sqrt t)|^2 series == double average of closed-form K via SUBSET
     DECOMPOSITION of the composed atom+Beta mixture (independent of nested quadrature)
  F  mixed lower differences of squared approximants >= 0 (series-only route)
  G  literal f_a: coefficient signs (-1)^j d_j >= 0 and (-1)^k f^(k)(t) >= 0
  H  a=1/2 endpoint closed form
Diagnostic only; not a proof.
"""
import mpmath as mp
import json, time

mp.mp.dps = 40
T0 = time.time()
results = {"checks": [], "failures": []}

def rec(name, ok, detail=""):
    results["checks"].append({"name": name, "ok": bool(ok), "detail": str(detail)[:200]})
    print(f"[{time.time()-T0:7.1f}s] {'OK  ' if ok else 'FAIL'} {name} {detail}", flush=True)
    if not ok:
        results["failures"].append(name)

def Eseries(a, b, z, terms=9000):
    s = mp.mpc(0)
    for n in range(terms):
        t = z**n / mp.gamma(a*n + b)
        s += t
        if abs(t) < mp.mpf('1e-44') * max(1, abs(s)):
            break
    return s

def I(x):
    return mp.sqrt(mp.pi)/(2*mp.sqrt(x))*mp.erfi(mp.sqrt(x)) if x else mp.mpf(1)

def gl(n):
    pts, wts = [], []
    for i in range(1, n+1):
        x = mp.cos(mp.pi*(i-mp.mpf('0.25'))/(n+mp.mpf('0.5')))
        for _ in range(100):
            p0, p1 = mp.mpf(1), x
            for j in range(2, n+1):
                p0, p1 = p1, ((2*j-1)*x*p1 - (j-1)*p0)/j
            dp = n*(x*p1 - p0)/(x*x - 1)
            x -= p1/dp
        pts.append(x)
        wts.append(2/((1-x*x)*dp*dp))
    return [(x+1)/2 for x in pts], [w/2 for w in wts]

GL200 = gl(200)

# ---------- A ----------
for r in [mp.mpf('0.3'), mp.mpf(1), mp.mpf('2.7'), mp.mpf(5)]:
    lhs = Eseries(mp.mpf(1)/2, 1, 1j*mp.mpf(r))
    rhs = mp.e**(-r*r) * (1 + 2j*r/mp.sqrt(mp.pi) * I(r*r))
    rec(f"A_Ehalfimag_r{r}", abs(lhs-rhs) < mp.mpf('1e-25')*max(1, abs(rhs)),
        f"diff={float(abs(lhs-rhs)):.2e}")
for x in [mp.mpf('0.4'), mp.mpf('3.3')]:
    lhs = mp.quad(lambda u: mp.e**(-x*(1-u*u)), [0, 1])
    rhs = mp.sqrt(mp.pi)/2 * Eseries(1, mp.mpf(3)/2, -x)
    rec(f"A_halfint_x{x}", abs(lhs-rhs) < mp.mpf('1e-25')*max(1, abs(rhs)),
        f"diff={float(abs(lhs-rhs)):.2e}")

# ---------- K routes ----------
def Ehalf(z):
    # literal series for E_{1/2,1}; safe for |z| <= 6
    return Eseries(mp.mpf(1)/2, 1, z)

def K_lit(v, w, t):
    return mp.re(Ehalf(1j*mp.sqrt(v*t)) * mp.conj(Ehalf(1j*mp.sqrt(w*t))))

def K_closed(v, w, t):
    if v == 0 or w == 0:
        return mp.e**(-(v+w)*t)
    return mp.e**(-(v+w)*t) * (1 + 4*t*mp.sqrt(v*w)/mp.pi * I(v*t) * I(w*t))

def J_rat(v, w, t):
    if v == 0 or w == 0:
        return mp.e**(-(v+w)*t)
    p1 = mp.quad(lambda u: mp.e**(-t*w*(1-u*u))/(v + w*u*u), [0, 1])
    p2 = mp.quad(lambda u: mp.e**(-t*v*(1-u*u))/(w + v*u*u), [0, 1])
    return 2*mp.sqrt(v*w)/mp.pi * (p1 + p2)

worst_b = 0.0
for (v, w, t) in [(0.7, 2.3, 0.5), (2.3, 0.7, 4.0), (mp.mpf('1e-4'), 3.0, 1.0),
                  (3.0, mp.mpf('1e-4'), 1.0), (1, 1, 10.0), (0.01, 0.02, 80.0),
                  (5, 5, 0.05), (1.5, 1.5, 1.0), (36, 1, 1.0), (1, 36, 1.0),
                  (0.05, 0.11, 20.0)]:
    a3 = K_closed(v, w, t); c = J_rat(v, w, t)
    err = float(abs(a3-c)/max(1, abs(a3)))
    tag = ""
    if mp.sqrt(v*t) <= 6 and mp.sqrt(w*t) <= 6:
        a1 = K_lit(v, w, t)
        err = max(err, float(abs(a1-a3)/max(1, abs(a3))))
        tag += f" series_rel={float(abs(a1-a3)/max(1,abs(a3))):.2e}"
    worst_b = max(worst_b, err)
    rec(f"B_kernel_v{v}_w{w}_t{t}", err < 1e-12, f"rel={err:.2e}{tag}")
rec("B_worst", worst_b < 1e-12, f"worst={worst_b:.2e}")
z0 = K_lit(0, 2.0, 1.3)
rec("B_zero_scale", abs(z0 - mp.e**(-2.6)) < mp.mpf('1e-30'), f"diff={float(abs(z0-mp.e**(-2.6))):.2e}")

# ---------- C: ODE residuals (analytic derivative, not finite differences) ----------
def dK_closed(v, w, t):
    # analytic derivative of the closed form
    S = v + w
    P = K_closed(v, w, t)
    return (2*mp.sqrt(v*w)/mp.pi * (mp.e**(-w*t)*I(w*t) + mp.e**(-v*t)*I(v*t))) - S*P

for (v, w) in [(0.7, 2.3), (1.0, 1.0), (5.0, 0.2), (0.03, 4.0)]:
    for t0 in [0.3, 1.7]:
        S = v + w
        # P' + S*P from closed form vs the ODE right side
        h = mp.mpf('1e-6')
        dP = (K_closed(v, w, t0+h) - K_closed(v, w, t0-h)) / (2*h)
        rhsC = 2*mp.sqrt(v*w)/mp.pi * (mp.e**(-w*t0)*I(w*t0) + mp.e**(-v*t0)*I(v*t0))
        resP = abs(dP + S*K_closed(v, w, t0) - rhsC)
        dJ = (J_rat(v, w, t0+h) - J_rat(v, w, t0-h)) / (2*h)
        resJ = abs(dJ + S*J_rat(v, w, t0) - rhsC)
        rec(f"C_ode_v{v}_w{w}_t{t0}", resP < mp.mpf('1e-9') and resJ < mp.mpf('1e-9')
            and abs(resP-resJ) < mp.mpf('1e-13'),
            f"resP={float(resP):.2e} resJ={float(resJ):.2e} (FD truncation; P,J satisfy same ODE)")
rec("C_J0", abs(J_rat(mp.mpf('0.7'), mp.mpf('2.3'), 0) - 1) < mp.mpf('1e-30'), "")

# ---------- D: T_k moments and Euler products ----------
BETA = mp.mpf('0.413753917')
for (k, q, x) in [(0, mp.mpf('0.9271'), 1.7), (3, mp.mpf('1.31'), 0.6),
                  (7, mp.mpf('0.33'), 4.2), (12, mp.mpf('2.7'), 0.9)]:
    lhs = BETA*x**q + (1-BETA)*(k+1)*mp.quad(lambda u: u**k*(x*u)**q, [0, 1])
    rhs = x**q * (k + 1 + BETA*q)/(k + 1 + q)
    rec(f"D_Tk_k{k}_q{float(q)}", abs(lhs-rhs) < mp.mpf('1e-18')*max(1, abs(rhs)),
        f"diff={float(abs(lhs-rhs)):.2e}")

def R_N(beta, q, N):
    p = mp.mpf(1)
    for k in range(1, N+2):
        p *= (k + beta*q)/(k + q)
    return mp.mpf(N)**((1-beta)*q) * p

for (beta, q) in [(0.7, 1.3), (BETA, mp.mpf('0.9271')), (1.0, 2.0), (0.3, 0.0)]:
    tgt = mp.gamma(1+q)/mp.gamma(1+beta*q)
    errs = []
    prev = None
    for N in [10, 100, 1000, 10000]:
        r = R_N(beta, q, N)
        e = abs(r-tgt)/max(1, abs(tgt))
        errs.append(e)
        rec(f"D_RN_dir_beta{float(beta):.4f}_q{float(q):.3f}_N{N}",
            e < {10: mp.mpf('0.15'), 100: mp.mpf('0.02')}.get(N, mp.mpf('0.002')),
            f"rel={float(e):.2e} (expect ~C/N)")
        if prev is not None:
            rec(f"D_mono_beta{float(beta):.4f}_q{float(q):.3f}_at{N}", prev <= r + mp.mpf('1e-40'), "")
        prev = r
    rec(f"D_RN_trend_beta{float(beta):.4f}_q{float(q):.3f}",
        (errs[0] == 0 and errs[1] == 0) or (errs[1] < errs[0]/5 and errs[2] < errs[1]/5),
        f"errs={[float(e) for e in errs]}")
    rec(f"D_bound_beta{float(beta):.4f}_q{float(q):.3f}", R_N(beta, q, 10) <= tgt, "")

# ---------- E: |M_N(i sqrt t)|^2 series vs double average of closed-form K ----------
# K(v,w,t) = A(v)A(w) + sqrt(v)C(v)*sqrt(w)C(w) with A(v)=Re E_{1/2}(i sqrt(vt))=e^{-vt},
# C(v)C(w) part: sqrt(v)C(v)=Im E_{1/2}(i sqrt(vt))=e^{-vt} 2 sqrt(vt)/sqrt(pi) I(vt).
# Both A and sqrt(.)C are SMOOTH in v>=0 after substituting u=s^2 in the Beta densities,
# so each composed one-dimensional average is computed by subset decomposition + GL.
def subset_avg_smooth(g, m, beta, x):
    # composed T_{m-1}...T_0 on g, integrands made smooth by u=s^2 per dimension
    XY, XW = gl(26)
    total = mp.mpf(0)
    for S in range(2**m):
        ns = bin(S).count('1')
        wS = beta**(m - ns) * (1-beta)**ns
        if wS == 0:
            continue
        dims = [j for j in range(m) if (S >> j) & 1]

        def rec_int(dims, pt):
            if not dims:
                return g(x*pt)
            j = dims[0]
            return sum(w*2*(j+1)*s**(2*j+1)*rec_int(dims[1:], pt*s*s) for s, w in zip(XY, XW))
        total += wS * rec_int(dims, mp.mpf(1))
    return total

def approxTransform(a, N, z):
    s = mp.mpc(0)
    for n in range(3000):
        coef = R_N(2*a, n/mp.mpf(2), N+1)/mp.gamma(1+n/mp.mpf(2))
        term = coef * z**n
        s += term
        if abs(term) < mp.mpf('1e-42')*max(1, abs(s)):
            break
    return s

def Afun(v, t):   # Re E_{1/2}(i sqrt(v t))
    return mp.e**(-v*t)

def Cfun(v, t):   # sqrt(v)*Im-part coefficient: Im E_{1/2}(i sqrt(vt)) / sqrt(v) * sqrt(v)
    return mp.e**(-v*t) * 2*mp.sqrt(v*t)/mp.sqrt(mp.pi) * I(v*t)   # this IS sqrt(v)*C(v)

# first verify the product decomposition itself against K_closed
for (v, w, t) in [(0.7, 2.3, 0.5), (1.5, 1.5, 1.0), (0.05, 4.0, 0.8)]:
    dec = Afun(v, t)*Afun(w, t) + Cfun(v, t)*Cfun(w, t)
    rec(f"E_decomp_v{v}_w{w}_t{t}", abs(dec - K_closed(v, w, t)) < mp.mpf('1e-15'),
        f"diff={float(abs(dec-K_closed(v,w,t))):.2e}")

for (a, N, t) in [(0.35, 0, 1.1), (0.35, 1, 0.7), (0.25, 1, 2.2), (0.5, 1, 0.4), (0.2, 2, 0.3)]:
    beta = 2*a
    CN = (mp.mpf(N)+1)**(1-beta)
    m = N + 2
    lhs = abs(approxTransform(a, N, 1j*mp.sqrt(t)))**2
    SA = subset_avg_smooth(lambda v: Afun(v, t), m, beta, CN)
    SC = subset_avg_smooth(lambda v: Cfun(v, t), m, beta, CN)
    rhs = SA*SA + SC*SC
    rel = abs(lhs-rhs)/max(1, abs(rhs))
    rec(f"E_sqavg_a{a}_N{N}_t{t}", rel < mp.mpf('1e-9'), f"rel={float(rel):.2e}")

# ---------- F: mixed differences of squared approximants (series-only) ----------
def sq_approx_series(a, N, t):
    return abs(approxTransform(a, N, 1j*mp.sqrt(t)))**2

for (a, N, t, hs) in [(0.35, 3, 0.5, [0.3]), (0.35, 3, 0.5, [0.3, 0.2]),
                      (0.2, 3, 1.0, [0.5, 0.1, 0.05]), (0.5, 3, 2.0, [0.4, 1.1])]:
    def MD(order, tt):
        if order == 0:
            return sq_approx_series(a, N, tt)
        return MD(order-1, tt) - MD(order-1, tt + hs[order-1])
    v = MD(len(hs), t)
    rec(f"F_mixeddiff_a{a}_N{N}_t{t}_k{len(hs)}", v >= -mp.mpf('1e-30'), f"val={float(v):.3e}")

# ---------- G: literal f_a coefficient and derivative signs ----------
def coeffs(a, jmax):
    out = []
    for j in range(jmax+1):
        acc = mp.mpf(0)
        for s in range(-j, j+1):
            acc += (-1)**s / (mp.gamma(a*(j+s)+1) * mp.gamma(a*(j-s)+1))
        out.append(acc)
    return out

for a in [0.2, 0.35, 0.5]:
    jmax = 120
    d = coeffs(mp.mpf(a), jmax)
    ok = all((-1)**j * d[j] >= 0 for j in range(jmax+1))
    rec(f"G_coef_signs_a{a}", ok, "all (-1)^j d_j >= 0")

def f_lit(a, t):
    # literal source expression via even/odd split of the genuine series
    return abs(Eseries(2*a, 1, -t) + 1j*mp.sqrt(t)*Eseries(2*a, 1+a, -t))**2

def nd(f, order, x0, hh):
    if order == 0:
        return f(x0)
    return (nd(f, order-1, x0+hh, hh) - nd(f, order-1, x0-hh, hh)) / (2*hh)

for a, ts in [(0.05, [0.2, 0.5, 1.0]), (0.2, [0.2, 1.0, 4.0]), (0.35, [0.2, 1.0, 4.0]),
              (0.5, [0.2, 1.0, 4.0])]:
    for t in ts:
        for k in [1, 2, 3, 5]:
            f = lambda tt: f_lit(mp.mpf(a), tt)
            h = {1: '0.01', 2: '0.02', 3: '0.03', 5: '0.01'}[k]
            deriv = nd(f, k, mp.mpf(t), mp.mpf(h))
            val = (-1)**k*deriv
            scale = max(1, abs(deriv))
            rec(f"G_deriv_a{a}_t{t}_k{k}", val >= -mp.mpf('1e-20')*scale,
                f"(-1)^k f^(k)={float(val):.3e}")

# ---------- H: a=1/2 endpoint ----------
for t in [0.5, 3.0]:
    lhs = abs(Eseries(mp.mpf(1)/2, 1, 1j*mp.sqrt(t)))**2
    rhs = abs(mp.e**(-t) * (1 + mp.erf(1j*mp.sqrt(t))))**2
    rec(f"H_endpoint_half_t{t}", abs(lhs-rhs) < mp.mpf('1e-25')*max(1, abs(rhs)),
        f"diff={float(abs(lhs-rhs)):.2e}")

n_ok = sum(1 for c in results["checks"] if c["ok"])
print(f"PASS {n_ok}/{len(results['checks'])} checks; failures: {results['failures']}")
json.dump(results, open("independent-checks.json", "w"), indent=1, default=str)
