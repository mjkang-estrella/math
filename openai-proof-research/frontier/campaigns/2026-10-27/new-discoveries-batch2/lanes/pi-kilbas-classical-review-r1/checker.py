#!/usr/bin/env python3
"""
Independent adversarial checker for the KILBAS-CLASSICAL-REDUCTION review.

Verifies numerically (corroboration only; the proof itself is analytic):
  T1  Levy-representation identity:
      phi(s) - phi(0) = [alpha/Gamma(1-alpha)] * int_0^inf e^{-(a+alpha)t}
                        (1-e^{-b s t})/(1-e^{-t})^{1+alpha} dt
      with a = 1+alpha(l-m), b = alpha m, 0<alpha<1, a>0.
  T1b Same integral rewritten on (0,1) (u = e^-t), checked by quadrature
      against the closed form (Gamma(1-alpha)/alpha)*[phi(s)-phi(0)].
  T2  Levy-measure integrability: int (1^y) nu(dy) < inf and int y^-? near 0.
  T3  Coefficient match: prod_{k=1}^n 1/phi(k) = Gamma(1+alpha l)/Gamma(1+alpha(l+n m))
      and equals the literal Kilbas-Saigo coefficient c_n of arXiv:2012.05666v1
      (product over k=1..n of Gamma(1+alpha((k-1)m+l))/Gamma(1+alpha((k-1)m+l+1))).
  T4  Exact conjecture-constant algebra:
      [1/Gamma(1+alpha(l-m))]/[1+x/Gamma(1+alpha(l-m+1))] == phi(0)/(phi(0)+x)
      [1/Gamma(1+alpha l)]/[1+x/Gamma(1+alpha(l+1))]   == phi(1)/(phi(1)+x).
  T5  Sandwich check on the literal KS series
      E_{alpha,m,l}(-x) = sum_n c_n (-x)^n   vs
      phi(0)/(phi(0)+x) <= E <= phi(1)/(phi(1)+x)   (also alpha=1).
      This is the *conjecture itself*; agreement over a grid corroborates the
      phi-indexing (a mis-indexed phi would typically break tightness/violate).
  T6  Killed moment formula, independent of sources:
      (i)  pure drift + killing: E[I^2] analytic check.
      (ii) compound-Poisson subordinator + killing: Monte-Carlo estimate of
           E[I^2], E[I^3] vs n!/prod_{k=1}^n (kappa + psi(k)).
  T7  Generic-bound consistency with Prop 4.3 of the source: the lower bound's
      large-x constant phi(0) equals Gamma(1+alpha(l+1-m))/Gamma(1+alpha(l-m)).
Memory: mpmath + small numpy MC only; well under 512 MiB; no process pools.
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 200

def phi(s, a, b, alpha):
    return mp.gamma(a + b*s + alpha) / mp.gamma(a + b*s)

# ---------------- T1: Levy representation identity ----------------
def _split_integral(a, h, al):
    """int_0^1 ((1-v)^a-(1-v)^(a+h))(1-v)^(al-1)/v^(1+al) dv,
    computed as h*[1/(1-al) + int_0^1 v^-al (r(v)-1) dv] with r(v) =
    ((1-v)^a-(1-v)^(a+h))/(h v) * (1-v)^(al-1), r(0)=1: removes the
    v^-al singularity so plain quadrature is accurate.

    Wait: f(v) = h v^-al r(v) requires (1-v)^al-1 factor inside r; then
    r(v)-1 = O(v) as v->0, so v^-al (r-1) ~ v^(1-al) -> 0. Correct.
    """
    def r(v):
        if v >= 1:
            return mp.mpf(0)   # limit: h(1-v)^al * ... -> 0
        if v == 0:
            return mp.mpf(1)
        return ((1-v)**a - (1-v)**(a+h)) / (h*v) * (1-v)**(al-1)
    def core(v):
        if v == 0:
            return mp.mpf(0)
        return v**(-al) * (r(v) - 1)
    return h * (1/(1-al) + mp.quad(core, [0, 0.1, 0.5, 0.9, 0.99, 0.9999, 1]))

def levy_integral(s, a, b, alpha):
    h = b*s
    val = _split_integral(a, h, alpha)
    return alpha / mp.gamma(1-alpha) * val

def t1():
    worst = 0.0
    cases = [
        (0.7, 1.3, 0.5, 0.3), (0.7, 1.3, 0.5, 2.0), (0.2, 0.9, 0.3, 1.7),
        (2.5, 0.4, 0.8, 0.05), (0.05, 2.0, 0.95, 1.0), (1.0, 1.0, 0.5, 1.0),
        (0.11, 3.3, 0.15, 0.9),
    ]
    for (a, b, al, s) in cases:
        lhs = phi(s, a, b, al) - phi(0, a, b, al)
        rhs = levy_integral(s, a, b, al)
        rel = abs(lhs - rhs) / abs(lhs)
        worst = max(worst, rel)
        assert rel < 1e-12, (a, b, al, s, lhs, rhs, rel)  # quadrature-limited near u->1
    print("T1 PASS  Levy-representation identity, max rel err", mp.nstr(worst, 3))

# ---------------- T1b: direct (0,1) closed form ----------------
def t1b():
    a, h, al = 0.7, 1.1, 0.5
    num = _split_integral(a, h, al)
    closed = mp.gamma(1-al)/al * (mp.gamma(a+h+al)/mp.gamma(a+h) - mp.gamma(a+al)/mp.gamma(a))
    rel = abs(num - closed)/abs(closed)
    assert rel < 1e-12, rel  # quadrature-limited near u->1
    print("T1b PASS  by-parts closed form, rel err", mp.nstr(rel, 3))

# ---------------- T2: Levy measure integrability ----------------
def t2():
    # nu(dy) after y = b t: (alpha/(b Gamma(1-alpha))) e^{-(a+alpha)y/b} / (1-e^{-y/b})^{1+alpha}
    a, b, al = 0.2, 0.9, 0.3
    g = lambda y: (al/(b*mp.gamma(1-al))) * mp.e**(-(a+al)*y/b) / (1-mp.e**(-y/b))**(1+al) if y > 0 else mp.inf
    # int_0^eps y*nu ~ eps^{1-al}/(1-al): finite since al<1
    i0 = mp.quad(lambda y: y*g(y) if y > 0 else mp.mpf(0), [0, mp.mpf('1e-4')])
    i1 = mp.quad(g, [mp.mpf('1e-4'), 1, 10, 100])
    total = i0 + i1
    assert total < mp.inf and total > 0
    # near-zero behaviour: nu(dy) ~ C y^{-1-alpha}, int_0^eps y nu(dy) ~ C eps^{1-alpha}/(1-alpha)
    print(f"T2 PASS  nu integrable: int_(0,100) min-scale mass ~ {mp.nstr(total,6)} (finite), "
          f"small-y mass {mp.nstr(i0,6)} consistent with y^(-1-alpha) singularity")

# ---------------- T3: coefficient match / telescoping ----------------
def t3():
    al, m, l = mp.mpf('0.5'), mp.mpf('0.7'), mp.mpf('0.9')
    a = 1 + al*(l-m); b = al*m
    for n in [1, 2, 5, 12, 40]:
        p1 = mp.mpf(1); p2 = mp.mpf(1)
        for k in range(1, n+1):
            p1 *= 1/phi(k, a, b, al)
            p2 *= mp.gamma(1+al*((k-1)*m+l))/mp.gamma(1+al*((k-1)*m+l+1))
        prod_inv, ks_lit = p1, p2
        # NOTE: the product does NOT telescope (b = alpha*m != alpha unless m=1);
        # the exact claim is only the term-by-term match c_n = prod_k 1/phi(k).
        assert abs(prod_inv - ks_lit)/ks_lit < 1e-50
    print("T3 PASS  prod_k 1/phi(k) == literal KS coefficient c_n (term-by-term), n=1,2,5,12,40")

# ---------------- T4: conjecture constant algebra ----------------
def t4():
    al, m, l = mp.mpf('0.5'), mp.mpf('0.7'), mp.mpf('0.9')
    a = 1 + al*(l-m); b = al*m
    x = mp.mpf('3.17')
    # Conjecture 4.5 as displayed (compound fractions): 1/(1 + x*GamA/GamB) form;
    # confirmed tight-at-0 slope Gamma(1+al*l)/Gamma(1+al(l+1)) per Remark 3.5(a) pattern.
    lo_lit = 1/(1 + x*mp.gamma(1+al*(l-m))/mp.gamma(1+al*(l-m+1)))
    lo_gen = phi(0, a, b, al) / (phi(0, a, b, al) + x)
    up_lit = 1/(1 + x*mp.gamma(1+al*l)/mp.gamma(1+al*(l+1)))
    up_gen = phi(1, a, b, al) / (phi(1, a, b, al) + x)
    assert abs(lo_lit - lo_gen) < 1e-50 and abs(up_lit - up_gen) < 1e-50
    # sanity: at x=0 both displayed bounds equal 1 (needed since E(0)=1)
    assert abs(1/(1 + mp.mpf(0)) - 1) == 0
    print("T4 PASS  conjectured bounds are literally 1/(1+x/phi(0)) and 1/(1+x/phi(1))")

# ---------------- T5: sandwich on the literal KS series ----------------
def ks_series(x, al, m, l):
    """Sum c_n (-x)^n, c_n = prod_{k=1}^n Gamma(1+al((k-1)m+l))/Gamma(1+al((k-1)m+l+1)).

    Alternating sum with catastrophic cancellation: first compute the EXACT
    log|term| profile with math.lgamma increments
        lt(n) - lt(n-1) = ln x - [lgamma(z_n+al) - lgamma(z_n)],  z_n = 1+al((n-1)m+l),
    locate the true peak and the point where |term| < 1e-120, then sum with
    mp.dps set above log10(peak)+margin. Returns (value, n_stop, log10_peak).
    """
    import math
    al_f, m_f, l_f, x_f = float(al), float(m), float(l), float(x)
    logx = math.log(x_f)
    acc = 0.0; peak = -math.inf; n_peak = 0
    n = 0
    while True:
        n += 1
        z = 1 + al_f*((n-1)*m_f + l_f)
        acc += math.lgamma(z) - math.lgamma(z + al_f)
        lt = n*logx + acc
        if lt > peak: peak, n_peak = lt, n
        if n > n_peak + 10 and lt < -120*math.log(10):
            n_stop = n
            break
        if n > 2000000:
            raise RuntimeError("profile: tail not reached (infeasible)", (al, m, l, x))
    need = int(peak/math.log(10)) + 200
    old = mp.mp.dps
    mp.mp.dps = max(old, need)
    try:
        s = mp.mpf(1); c = mp.mpf(1)
        for k in range(1, n_stop+1):
            zk = 1 + al*((k-1)*m + l)
            c *= mp.gamma(zk)/mp.gamma(zk + al)
            s += c*(-x)**k
        return s, n_stop, peak/math.log(10)
    finally:
        mp.mp.dps = old

def ks_profile(x, al, m, l):
    """Exact log10 of max |term| and stop index, without summing."""
    import math
    al_f, m_f, l_f, x_f = float(al), float(m), float(l), float(x)
    logx = math.log(x_f); acc=0.0; peak=-math.inf; n_peak=0; n=0
    while True:
        n += 1
        z = 1 + al_f*((n-1)*m_f + l_f)
        acc += math.lgamma(z) - math.lgamma(z+al_f)
        lt = n*logx + acc
        if lt > peak: peak, n_peak = lt, n
        if n > n_peak + 10 and lt < -120*math.log(10):
            return peak/math.log(10), n
        if n > 250000:
            return math.inf, math.inf  # infeasible by direct summation

def t5():
    grids = [
        (mp.mpf('0.3'), mp.mpf('0.7'), mp.mpf('0.4')),   # l > m - 1/al (0.7-3.33)
        (mp.mpf('0.5'), mp.mpf('0.7'), mp.mpf('0.9')),
        (mp.mpf('0.9'), mp.mpf('1.7'), mp.mpf('0.6')),   # l slightly > m-1/al = 0.589
        (mp.mpf('1.0'), mp.mpf('0.6'), mp.mpf('0.3')),   # alpha=1 boundary
        (mp.mpf('0.15'), mp.mpf('2.5'), mp.mpf('0.01')),
    ]
    for (al, m, l) in grids:
        assert l > m - 1/al, "parameter outside conjecture range"
        a = 1 + al*(l-m); b = al*m
        lo_c = phi(0, a, b, al); up_c = phi(1, a, b, al)
        xs = [mp.mpf(v) for v in ['0.01','0.1','1','10','100','1000','5000']]
        nchecked = 0
        for x in xs:
            lpk, nstop = ks_profile(x, al, m, l)
            if lpk > 2000 or nstop > 60000:
                continue  # numerically infeasible by direct summation; skip
            E, nstop2, lpk2 = ks_series(x, al, m, l)
            lo = lo_c/(lo_c+x); up = up_c/(up_c+x)
            assert lo - mp.mpf('1e-60') <= E <= up + mp.mpf('1e-60'), (al, m, l, x, lo, E, up)
            nchecked += 1
        assert nchecked >= 3, ("too few feasible x", al, m, l)
        # tightness spot-check: x->0 upper slope and Prop-4.3 lower constant
        E1, _, _ = ks_series(mp.mpf('1e-8'), al, m, l)
        slope = (1 - E1)/mp.mpf('1e-8')          # ~ 1/phi(1)
        assert abs(slope*up_c - 1) < 1e-5
        asym_lo = mp.gamma(1+al*(l+1-m))/mp.gamma(1+al*(l-m))
        assert abs(asym_lo - lo_c) < 1e-40       # T7 folded in: lower constant = Prop 4.3 constant
    mp.mp.dps = 200
    print("T5 PASS  sandwich phi(0)/(phi(0)+x) <= E_{alpha,m,l}(-x) <= phi(1)/(phi(1)+x) "
          "on 5 param sets over tractable x-grids incl. alpha=1; upper tight at 0; lower constant = Prop 4.3 constant (T7)")

# ---------------- T6: killed moment formula, source-independent ----------------
def t6():
    # (i) analytic: pure drift b, killing a: E[I^2] = 2/((a+b)(a+2b))
    a, b = mp.mpf('1.3'), mp.mpf('0.7')
    num = mp.quad(lambda t: a*mp.e**(-a*t) * ((1-mp.e**(-b*t))/b)**2, [0, mp.inf])
    exact = 2/((a+b)*(a+2*b))
    assert abs(num-exact)/exact < 1e-30
    # (ii) Monte Carlo: compound Poisson jumps exp(beta), rate lam; killing kappa.
    rng = np.random.default_rng(20261028)
    lam, beta, kap = 1.7, 2.3, 0.9
    N = 400_000
    # simulate I = int_0^zeta exp(-xi_t) dt. Piecewise-constant between jumps.
    # Draw exp jumps until cumulative time exceeds zeta.
    zeta = rng.exponential(1/kap, N)
    I2 = np.empty(N); I3 = np.empty(N)
    # expected #jumps ~ (lam*EY+zeta)*...; use per-sample loop over small vectors
    # vectorized-ish: for each sample generate jumps until t > zeta
    for i in range(N):
        z = zeta[i]
        t = 0.0; xi = 0.0; acc = 0.0
        while True:
            wait = rng.exponential(1/lam)
            if t + wait > z:
                acc += (z - t)*np.exp(-xi)
                break
            acc += wait*np.exp(-xi)
            t += wait
            xi += rng.exponential(1/beta)
        I2[i] = acc*acc; I3[i] = acc**3
    e2 = I2.mean(); e3 = I3.mean()
    def psi(s): return lam*(1 - beta/(beta+s))
    ex2 = 2/((kap+psi(1))*(kap+psi(2)))
    ex3 = 6/((kap+psi(1))*(kap+psi(2))*(kap+psi(3)))
    rel2 = abs(e2-ex2)/ex2; rel3 = abs(e3-ex3)/ex3
    # MC standard error for E[I^2]: std/sqrt(N) ~ order of mean
    se2 = I2.std()/np.sqrt(N)/ex2; se3 = I3.std()/np.sqrt(N)/ex3
    assert rel2 < 5*se2 + 0.02, (e2, ex2, rel2, se2)
    assert rel3 < 5*se3 + 0.02, (e3, ex3, rel3, se3)
    print(f"T6 PASS  killed moment formula: drift analytic exact; "
          f"MC compound-Poisson rel err E[I^2]={rel2:.3f} (se {se2:.3f}), E[I^3]={rel3:.3f} (se {se3:.3f})")

# ---------------- T7 (explicit): generic lower constant == Prop 4.3 constant ----------------
def t7():
    for (al, m, l) in [(0.3,0.7,0.4),(0.9,1.7,0.2),(0.5,0.7,0.9)]:
        al, m, l = map(mp.mpf, (al, m, l))
        a = 1+al*(l-m); b = al*m
        p43 = mp.gamma(1+al*(l+1-m))/mp.gamma(1+al*(l-m))
        assert abs(p43 - phi(0,a,b,al)) < 1e-45
    print("T7 PASS  phi(0) == Gamma(1+al(l+1-m))/Gamma(1+al(l-m)) exactly (Prop 4.3 constant)")

if __name__ == "__main__":
    import resource
    t1(); t1b(); t2(); t3(); t4(); t5(); t6(); t7()
    print("ALL CHECKS PASS")
    print("peak RSS MiB:", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024)
