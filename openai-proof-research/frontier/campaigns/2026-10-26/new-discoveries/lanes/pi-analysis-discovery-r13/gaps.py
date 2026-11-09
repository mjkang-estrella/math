"""Gap analysis for the Key Lemma L(k,mu): A_{k+1}(mu)/A_k(mu) >= beta(x), x=k/mu,
beta(x) = 1 + x - psi(x).

Also test candidate simpler sufficient lemmas:
  L2: A_{k-1}(mu)/A_k(mu) >= (1/mu^2)(1 - psi(x)/x)   [via (1+1/J)^k >= 1+k/J, k>=1]
  scaling guess: A_{k+1}(mu)/A_k(mu) >= B_{x+1}/B_x ?
"""
from mpmath import mp, mpf, log, exp
import sys
sys.path.insert(0, '.')
from numerics import moment_converged, _saddle_j, _log_fact

mp.dps = 60

def A(k, mu):
    v, ok = moment_converged(k, mu)
    return v / mpf(mu)**mpf(k)

def Bx(x):
    v, ok = moment_converged(x, 1)
    return v

def f_fp(x):
    x = mpf(x)
    s1, ok1 = moment_converged(x, 1)
    # derivative sum with convergence
    prev = None
    for extra in (30, 60, 120):
        jsad = _saddle_j(x, mpf(1))
        sigma = (jsad/(log(jsad)+1)+1)**mpf('0.5') if jsad > 1 else mpf(5)
        jmax = int(jsad + extra*sigma + 100)
        s2 = mpf(0)
        for j in range(2, jmax+1):
            s2 += exp(x*log(j) - _log_fact(j) - 1)*log(j)
        if prev is not None and abs(s2-prev) < abs(prev)*mpf('1e-55'):
            break
        prev = s2
    return log(s1), s2/s1

def psi(x):
    f, fp = f_fp(x)
    return mpf(x)*fp - f

def beta(x):
    return 1 + mpf(x) - psi(x)

def main():
    print("psi/beta profile:")
    for x in ['0.1','0.25','0.4','0.5','0.8','1','1.5','2','3','4','6','10','20','50','100','320']:
        p = psi(x)
        print(f"x={x:>5} psi={float(p):>12.6f} psi/x={float(p/mpf(x)):>8.4f} beta={float(beta(x)):>12.6f}")
    print()
    print("Key-lemma gap g(k,mu) = A_{k+1}/A_k - beta(k/mu)  (want >=0):")
    ks = ['0.5','1','2','3','5','10','50']
    mus = ['0.1','0.2','0.5','1','2','5','10','100']
    for k in ks:
        for mu in mus:
            x = mpf(k)/mpf(mu)
            u = A(mpf(k)+1, mpf(mu))/A(k, mu)
            g = u - beta(x)
            print(f"k={k:>5} mu={mu:>5} x={float(x):>8.2f} u={float(u):>14.6f} beta={float(beta(x)):>12.6f} gap={float(g):>12.6f}")
    print()
    print("scaling guess: u(k,mu) vs B_{x+1}/B_x:")
    for k in ['2','3','10']:
        for mu in ['0.5','1','2','10']:
            x = mpf(k)/mpf(mu)
            u = A(mpf(k)+1, mpf(mu))/A(k, mu)
            r = Bx(x+1)/Bx(x)
            print(f"k={k:>4} mu={mu:>4} x={float(x):>7.2f} u={float(u):>12.6f} B_{float(x)+1}/B_{float(x)}={float(r):>12.6f} u-r={float(u-r):>10.6f}")

if __name__ == "__main__":
    main()
