"""High-precision numerics for surviving parts of Ahle Conjecture 1 (MathDB 350262). v3

Unified claim:  sign( D(k,mu) ) = sign(mu-1),
D(k,mu) = log A_k(mu) - mu*log B_{k/mu},
A_k(mu) = B(k,mu)/mu^k = E[(J/mu)^k], J~Poisson(mu);
B(k,mu) = e^-mu sum_{j>=0} j^k mu^j/j!  (Dobinski; = Touchard poly for integer k);
B_x = B(x,1) = e^-1 sum_{j>=0} j^x/j! = E[Y^x], Y~Poisson(1).

(A) mu>=1: A_k(mu) >= B_{k/mu}^mu  (Ahle lower bound, real mu; source proves integer mu only)
(B) 0<mu<=1: A_k(mu) <= B_{k/mu}^mu  (Ahle small-mu bound)
"""
from mpmath import mp, mpf, exp, log, sqrt
from fractions import Fraction
import sys

mp.dps = 70

def _log_fact(n):
    return log(mp.gamma(n + 1))

def _saddle_j(k, lam):
    """j* solving j*log(j/lam)=k (maximizer of term j^k lam^j/j!)."""
    k = mpf(k); lam = mpf(lam)
    if k <= lam:
        j = lam
    else:
        j = k / log(k/lam + 2)
    for _ in range(100):
        f = j*log(j/lam) - k
        fp = log(j/lam) + 1
        step = f/fp
        j = j - step
        if abs(step) < mpf('1e-40'):
            break
        if j <= 0:
            j = mpf('0.01')
    return max(j, mpf(1))

def poisson_moment(k, lam, extra=30):
    """E[J^k] for J~Poisson(lam), real k>0. Saddle-adaptive truncation."""
    k = mpf(k); lam = mpf(lam)
    js = _saddle_j(k, lam)
    logratio = log(js/lam) if (lam > 0 and js > lam) else mpf(1)
    sigma = sqrt(js/(logratio+1) + 1)
    jmax = int(js + extra*sigma + 100)
    jmax = max(jmax, 100)
    loglam = log(lam) if lam > 0 else mpf(0)
    emlam = exp(-lam)
    s = mpf(0)
    for j in range(1, jmax+1):
        s += exp(k*log(j) - _log_fact(j) + j*loglam) * emlam
    return s

def moment_converged(k, lam):
    vals = []
    for extra in (30, 60, 120):
        vals.append(poisson_moment(k, lam, extra))
    ok = all(abs(log(vals[i+1]) - log(vals[i])) < mpf('1e-55') for i in range(2))
    return vals[-1], ok

def B_x(x):
    v, ok = moment_converged(x, 1)
    return v, ok          # already includes e^-1

def A_k_mu(k, mu):
    v, ok = moment_converged(k, mu)
    return v / mpf(mu)**mpf(k), ok

def D(k, mu):
    a, ok1 = moment_converged(k, mu)
    b, ok2 = moment_converged(mpf(k)/mpf(mu), 1)
    d = log(a) - mpf(k)*log(mpf(mu)) - mpf(mu)*log(b)
    return d, (ok1 and ok2)

# ---------- exact integer cross-checks ----------
def stirling_row(n):
    """S(n,j) for j=0..n, exact ints."""
    row = [0]*(n+1); row[0] = 1
    for i in range(1, n+1):
        for j in range(i, 0, -1):
            row[j] = j*row[j] + row[j-1]
        row[0] = 0
    return row

def touchard_exact(k, mu_num, mu_den):
    """T_k(mu) exact Fraction for integer k."""
    row = stirling_row(k)
    s = Fraction(0)
    p = Fraction(1)
    mu = Fraction(mu_num, mu_den)
    for i in range(k+1):
        s += row[i]*mu**i
    return s

def bell_exact(n):
    return sum(stirling_row(n))

def check_pipeline(kmax=12, mus=((1,2),(3,2),(2,1),(1,3),(5,2),(10,1),(4,5))):
    """Compare float pipeline vs exact Touchard / Bell for integer k."""
    print("=== pipeline validation (integer k: Touchard exact) ===")
    worst = 0
    for k in range(1, kmax+1):
        for (pn, pd) in mus:
            mu = mpf(pn)/pd
            tex = touchard_exact(k, pn, pd)
            aex = tex / (Fraction(pn,pd)**k)
            v, ok = moment_converged(k, mu)
            afloat = v / mu**k
            rel = abs(log(afloat) - log(mp.mpf(aex.numerator)/mp.mpf(aex.denominator)))
            worst = max(worst, float(rel))
            if rel > mpf('1e-40'):
                print(f"MISMATCH k={k} mu={pn}/{pd} rel={float(rel)}")
    # Bell numbers via Dobinski vs exact
    for n in range(1, 30):
        v, ok = moment_converged(n, 1)
        bex = bell_exact(n)
        rel = abs(log(v) - log(mp.mpf(bex)))
        worst = max(worst, float(rel))
        if rel > mpf('1e-40'):
            print(f"MISMATCH B_{n}: float={float(log(v))} exact={bex}")
    print(f"pipeline worst log-rel error: {worst:.3e}")

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    if mode in ("all", "validate"):
        check_pipeline()
    if mode in ("all", "sweep"):
        print("=== sweep: sign(D(k,mu)) ?= sign(mu-1) ===")
        ks = [x for x in ['0.3','0.5','0.8','1','1.5','2','3','5','10','20','50','100','3200']]
        mus = [x for x in ['0.05','0.1','0.2','0.5','0.8','0.95','1','1.05','1.2','1.5','2','3','5','10','20','50','100']]
        bad = []; unconv = []
        for k in ks:
            for mu in mus:
                d, ok = D(k, mu)
                es = 1 if float(mu) > 1 else (-1 if float(mu) < 1 else 0)
                good = (d >= 0) if es >= 0 else (d <= 0)
                if not ok: unconv.append((k, mu))
                if not good: bad.append((k, mu, float(d)))
        print("violations:", bad if bad else "NONE")
        print("unconverged:", unconv if unconv else "NONE")
    if mode in ("all", "fine"):
        k = mpf(sys.argv[2]); lo, hi, n = mpf(sys.argv[3]), mpf(sys.argv[4]), int(sys.argv[5])
        for i in range(n+1):
            mu = lo + (hi-lo)*i/n
            d, ok = D(k, mu)
            print(f"mu={float(mu):>12.7f} D={float(d):>18.10f} conv={ok}")

if __name__ == "__main__":
    main()
