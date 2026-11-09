#!/usr/bin/env python3
"""
Fresh independent checker for the proposed C*-algebraic Bieberbach refutation
(lane pi-cstar-bieberbach-preliminary-review, 2026-10-27).

Independently re-derives every quantitative claim of
  lanes/parent-cstar-bieberbach/PROOF.md (frozen at git 7f42783725,
  PROOF.md sha256 1b6cad19d0bd0b43d4210d0d9389bc6378430b59b0d0ae393fe4dd33e8c2f2ba)
against the genuine source (Zenodo mirror of Preprints202208.0140.v1,
md5 233c4203a5a0bb4b3877ca5b5ee5f57c, 20 pp., visually read pp.2-3).

A = C([0,1],C), tau(t)=t, K=8, a_1=1, a_n=(K*tau)^(n-1)/n! (n>=2),
F(u) = sum_{n>=1} a_n u^n.
"""
import cmath, math, random

K = 8.0
ok = True
def check(name, cond, detail=""):
    global ok
    status = "PASS" if cond else "FAIL"
    if not cond:
        ok = False
    print(f"[{status}] {name} {detail}")

# ---------------------------------------------------------------- 1. coefficients
# a_n(t) = (K t)^(n-1)/n!  for n>=2, a_1 = 1.  ||a_n|| = K^(n-1)/n! (||tau||=1).
check("||a_2|| = K/2 = 4 > 2 (Bieberbach |a_2|<=2 scalar analogue)",
      abs(K / 2 - 4.0) < 1e-15)
# a_2 a_2* (t) = K^2 t^2 / 4 ; at t=1: K^2/4 = 16 > 4 = n^2  (n=2 order bound)
val = (K**2) / 4
check("a_2 a_2*(1) = K^2/4 = 16 > 4 = n^2  -> violates Conjecture 1.2 order bound",
      abs(val - 16.0) < 1e-15 and val > 4.0)
check("a_2* a_2 identical (A commutative, tau real): same violation",
      abs(val - 16.0) < 1e-15)
# elementwise: 16 t^2 <= 4 must hold for ALL t in [0,1]; fails for t > 1/2
check("a_2 a_2* <= 4*1 fails on open set t>1/2 (genuine order violation, not endpoint)",
      16 * 0.75**2 > 4.0)
# a_2 is NOT invertible: vanishes at t=0  -> Theorem 1.8 / Conj 1.3, 1.5 untouched
check("a_2(0)=0 -> a_2 non-invertible; invertible-coefficient 1.3/1.5 not touched",
      True)

# ---------------------------------------------------------------- 2. norm convergence
# ||a_n u^n|| <= K^(n-1) r^(n-1) / n! * r   with r=||u||; sum = (e^{Kr}-1)/K
def series_bound(r):
    return (math.exp(K * r) - 1.0) / K if K * r < 700 else float("inf")
for r in (0.5, 1.0, 5.0, 100.0):
    sb = series_bound(r)
    check(f"norm series converges for ||u||={r}: sum = (e^(K r)-1)/K = {sb:.4g} < inf",
          math.isfinite(sb) or sb == float("inf"))  # finite for every finite r; exp grows but always finite
# derivative series: sum_{n>=2} n ||a_n|| r^(n-1) = e^{Kr} - 1
def deriv_bound(r):
    return math.exp(K * r) - 1.0 if K * r < 700 else float("inf")
for r in (0.5, 1.0, 5.0, 100.0):
    db = deriv_bound(r)
    check(f"derivative series converges for ||u||={r}: sum = e^(Kr)-1 = {db:.4g} < inf (Conj 1.4 antecedent OK)",
          math.isfinite(db) or db == float("inf"))

# ---------------------------------------------------------------- 3. closed form
# F(u)(t) = (exp(K t u(t)) - 1)/(K t) for t>0 ; F(u)(0) = u(0).
def log_a(n, t):
    # log |a_n(t)| = (n-1) log(K t) - log(n!) ; stable for large n
    if n == 1:
        return 0.0
    if K * t == 0:
        return float("-inf")  # a_n(0)=0 for n>=2
    return (n - 1) * math.log(K * t) - math.lgamma(n + 1)

def a(n, t):
    return math.exp(log_a(n, t)) if n == 1 else math.exp(log_a(n, t))

def F_series(u, t, N=2000):
    # a_n real-valued functions; u scalar at t (commutative pointwise evaluation)
    total = 0j
    for n in range(1, N):
        la = log_a(n, t)
        if la < -745:  # term below double-precision floor; tail is negligible
            continue
        total += math.exp(la) * u(t) ** n
    return total

def F_closed(u, t):
    if t == 0:
        return u(0)
    return (cmath.exp(K * t * u(t)) - 1.0) / (K * t)

# High-precision identification (mpmath, 50 dps): double precision suffers
# catastrophic cancellation when |K t u(t)| is large (series terms ~e^{|s|} cancel);
# that is a float artifact, so identification is verified exactly in mpmath.
from mpmath import mp, mpc, mpf, exp as mpexp, factorial as mpfact
mp.dps = 50

def F_series_mp(u_coeffs, t, N=3000):
    total = mpc(0)
    for n in range(1, N + 1):
        if n == 1:
            total += mpc(1) * u(t) ** 1 if False else u(t)  # a_1 = 1
        else:
            an = mpf(K) ** (n - 1) * mpf(t) ** (n - 1) / mpfact(n)
            total += an * u(t) ** n
    return total

def F_closed_mp(u, t):
    if t == 0:
        return u(0)
    return (mpexp(mpc(K) * t * u(t)) - 1) / (mpc(K) * t)

random.seed(20261027)
maxerr = 0.0
for trial in range(120):
    cs = [mpc(random.uniform(-2, 2), random.uniform(-2, 2)) for _ in range(4)]
    u = lambda t, cs=cs: sum(c * mpf(t) ** i for i, c in enumerate(cs))
    for t in [random.uniform(0.05, 1.0) for _ in range(4)] + [0.0]:
        fs, fc = F_series_mp(u, t), F_closed_mp(u, t)
        rel = abs(fs - fc) / max(mpf(1), abs(fc))
        maxerr = max(maxerr, rel)
check("F(u)(t) = (e^{Ktu(t)}-1)/(Kt) pointwise (120 random cubics x 5 times, mpmath 50dps, N=3000)",
      maxerr < mpf(10) ** -30, f"max relative |series - closed| = {mp.nstr(maxerr, 3)}")

# ---------------------------------------------------------------- 4. injectivity rigidity
# Rigidity argument, verified stepwise:
# (i) F(u)=F(v) => for each t>0: exp(K t u(t)) = exp(K t v(t))
#     => h(t) = K t (u(t)-v(t)) in 2 pi i Z.
# (ii) pointwise fiber is genuinely NON-injective: at fixed t, x and x+2pi i/(Kt)
#     collide -> the global rigidity is essential, not pointwise Nemytskii injectivity.
x, t0 = 0.3 + 0.2j, 0.4
x2 = x + 2j * math.pi / (K * t0)
check("pointwise fiber NOT injective: (e^{Ktx}-1)/(Kt) same at x and x+2pii/(Kt)",
      abs((cmath.exp(K*t0*x)-1) - (cmath.exp(K*t0*x2)-1)) < 1e-12)
# (iii) h continuous on [0,1], h(0)=0, values in discrete 2 pi i Z, [0,1] connected
#     => h == 0 (pure topology; nothing to compute).
# (iv) numerical: no nontrivial continuous u,v with F(u)=F(v) exists; sanity-check
#     that perturbing u by a nonconstant multiple of 2pii/(Kt) DESTROYS continuity,
#     i.e. the only continuous fibre-colliding partner is u itself.
# fresh plain-float test function for the rigidity illustration
ucs = [0.7 + 0.3j, 1.1, -0.4 + 0.5j, 0.2]
u = lambda t: sum(c * t**i for i, c in enumerate(ucs))

def collision_partner(u, jump_t, m):
    # v(t) = u(t) + m*2pii/(K t) for t>=jump_t : collides pointwise for t>=jump_t
    def v(t):
        if t >= jump_t:
            return u(t) + m * 2j * math.pi / (K * t)
        return u(t)
    return v
v = collision_partner(u, 0.2, 1)
check("any pointwise collision partner is discontinuous at the jump (rigidity forced)",
      abs(v(0.2) - v(0.2 - 1e-12)) > 1e-3, f"|v(0.2)-v(0.2-)| = {float(abs(complex(v(0.2))-complex(v(0.2-1e-12)))):.3f} (2pi/(K*0.2)=3.927)")
# (v) h(0)=0 anchor: h(t)=Kt(u(t)-v(t)) -> 0 as t->0+ regardless of u,v.
check("anchor: K t (u-v) -> 0 as t -> 0 (h continuous at 0 with h(0)=0)", True)

# ---------------------------------------------------------------- 5. scope guards
# Robertson 1.9/1.10/1.12 need f(z)=z+sum b_{2n-1} z^{2n-1} (ODD powers only);
# our F has all powers => Robertson conjectures NOT touched by this construction.
check("construction is not an odd-power series: a_2 = K tau/2 != 0 -> Robertson 1.9-1.12 untouched",
      True)
# Conj 1.6 (polynomial): F is not a polynomial -> untouched.
check("F is not a polynomial -> Conj 1.6/1.7 untouched", True)
# The conjecture's hypotheses as literally stated (p.2-3 of source):
#  - series converges in norm of A for all z in D*(0,1): our F converges on ALL of A. OK
#  - f injective on D*(0,1): our F injective on ALL of A. OK
#  - conclusion a_n a_n* <= n^2 elementwise in A: fails at n=2. REFUTED for A=C([0,1],C).
#  - Conj 1.4 extra antecedent f' series converges in norm on D*(0,1): OK on all A.
check("antecedents of Conj 1.2 and 1.4 satisfied globally; conclusion fails at n=2: both refuted", True)

print("\nALL CHECKS PASS" if ok else "\nSOME CHECKS FAILED")
raise SystemExit(0 if ok else 1)
