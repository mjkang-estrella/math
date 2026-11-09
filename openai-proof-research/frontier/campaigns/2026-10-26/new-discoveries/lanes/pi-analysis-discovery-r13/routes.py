"""Test proof-route monotonicity conditions for Ahle 350262 surviving claims.

Route 1: R_k(mu) = A_k(mu)/B_{k/mu}^mu increasing in mu for each fixed k.
  d log R/dmu = A_{k+1}(mu)/A_k(mu) - 1 - x + psi(x),  x=k/mu,
  psi(x) = x f'(x) - f(x), f = log B_x, f'(x)=E[Y^x log Y]/E[Y^x].

Route 2 (MON): mu -> M(mu*x, mu)/mu increasing for each fixed x,
  M(k,mu) = log A_k(mu).
  d/dmu [M(mu x, mu)/mu] = [ x*d_k M + d_mu M - M/mu ] / mu  at k=mu x,
  d_k M = E_tilt[log(J/mu)] (tilt j^k mu^j/j!),  d_mu M = A_{k+1}/A_k - 1 - x.
"""
from mpmath import mp, mpf, log, exp
import sys
sys.path.insert(0, '.')
from numerics import moment_converged, A_k_mu, B_x, D

mp.dps = 60

def f_and_fprime(x):
    """f(x)=log B_x, f'(x)=E[Y^x log Y]/B_x for Y~Poisson(1)."""
    x = mpf(x)
    num, _ = moment_converged((x, 'log'), 1) if False else (None, None)
    # compute sum j^x log j / j! * e^-1 and sum j^x/j!*e^-1
    def sums(lam, extra=30):
        lam = mpf(lam)
        js = mpf(x)
        # saddle for j^x log j is same as j^x
        from numerics import _saddle_j, _log_fact
        jsad = _saddle_j(x, lam)
        import math
        sigma = 30
        jmax = int(jsad + 60*max(1, mpf(1)) + 200)  # generous
        jmax = max(jmax, 200)
        s1 = mpf(0); s2 = mpf(0)
        emlam = exp(-lam); loglam = log(lam) if lam > 0 else mpf(0)
        for j in range(1, jmax+1):
            t = exp(x*log(j) - _log_fact(j) + j*loglam)*emlam
            s1 += t
            s2 += t*log(j)
        return s1, s2
    s1a, ok1 = moment_converged(x, 1)
    # derivative sum: use same truncation growth check
    s2 = None
    prev = None
    for extra in (30, 60, 120):
        from numerics import _saddle_j, _log_fact
        jsad = _saddle_j(x, mpf(1))
        sigma = (jsad/(log(jsad)+1)+1)**mpf('0.5') if jsad > 1 else mpf(5)
        jmax = int(jsad + extra*sigma + 100)
        s2 = mpf(0)
        for j in range(2, jmax+1):
            s2 += exp(x*log(j) - _log_fact(j) - 1)*log(j)
        if prev is not None and abs(s2 - prev) < abs(prev)*mpf('1e-55'):
            break
        prev = s2
    return log(s1a), s2/s1a

def psi(x):
    f, fp = f_and_fprime(x)
    return mpf(x)*fp - f

def route1_point(k, mu):
    """d log R / d mu at (k,mu): should be >= 0 if Route 1 holds."""
    k = mpf(k); mu = mpf(mu); x = k/mu
    ak, ok1 = moment_converged(k, mu)
    ak1, ok2 = moment_converged(k+1, mu)
    ratio = (ak1/ mpf(mu)**(k+1)) / (ak / mpf(mu)**k)  # A_{k+1}/A_k
    p = psi(x)
    return ratio - 1 - x + p, ok1 and ok2

def route2_point(x, mu):
    """d/dmu [M(mu x, mu)/mu] * mu  (sign test): should be >= 0."""
    x = mpf(x); mu = mpf(mu); k = mu*x
    ak, ok1 = moment_converged(k, mu)
    ak1, ok2 = moment_converged(k+1, mu)
    ratio = (ak1/mpf(mu)**(k+1))/(ak/mpf(mu)**k)
    # d_k M = E_tilt[log(J/mu)] with tilt j^k mu^j/j!
    from numerics import _saddle_j, _log_fact
    jsad = _saddle_j(k, mu)
    sigma = (jsad/(log(jsad/mu)+1)+1)**mpf('0.5') if jsad > mu else mpf(5)
    jmax = int(jsad + 60*sigma + 200)
    num = mpf(0); den = mpf(0)
    emlam = exp(-mu); loglam = log(mu)
    for j in range(1, jmax+1):
        t = exp(k*log(j) - _log_fact(j) + j*loglam)*emlam
        num += t*log(j/mu)
        den += t
    dkM = num/den
    dmuM = ratio - 1 - x
    M = log(ak/mpf(mu)**k)
    val = x*dkM + dmuM - M/mu
    return val, True

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "r1"
    if mode == "validate_psi":
        # psi(1) should equal f'(1)... f(1)=0, B_2/B_1 = 2: check known identities
        for x in ['0.25','0.5','1','2','4','10']:
            f, fp = f_and_fprime(x)
            print(f"x={x}: f={float(f):.6f} f'={float(fp):.6f} psi={float(psi(x)):.6f}")
    if mode == "r1":
        print("=== Route 1: d log R/dmu >= 0 ? ===")
        bad = []
        ks = ['0.3','0.5','1','2','3','5','10','20','50','100','3200']
        mus = ['0.05','0.1','0.2','0.5','0.8','1','1.2','1.5','2','3','5','10','20','50','100']
        for k in ks:
            for mu in mus:
                v, ok = route1_point(k, mu)
                if v < 0:
                    bad.append((k, mu, float(v)))
        print("route1 failures:", bad if bad else "NONE")
    if mode == "r2":
        print("=== Route 2 (MON) ===")
        bad = []
        xs = ['0.3','0.5','1','2','3','5','10','20','50']
        mus = ['0.05','0.1','0.2','0.5','0.8','1','1.2','1.5','2','3','5','10','20','50']
        for x in xs:
            for mu in mus:
                v, ok = route2_point(x, mu)
                if v < 0:
                    bad.append((x, mu, float(v)))
        print("route2 failures:", bad if bad else "NONE")

if __name__ == "__main__":
    main()
