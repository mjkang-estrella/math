from mpmath import mp, mpf, gamma, gammainc, sqrt, exp, pi, erf, findroot, quad, inf, odefun
mp.dps = 40

def F_VG(x, r, theta, sigma, mu=0):
    a = mpf(r)/2; lam = mpf(1)/2
    x = mpf(x)-mu; theta = mpf(theta); sigma = mpf(sigma)
    def Fs(s):  # regularized lower gamma P(a, lam*s)
        return gammainc(a, 0, lam*s, regularized=True)
    def integrand(z):
        disc = sqrt((sigma*z)**2 + 4*theta*x)
        y2 = (-sigma*z + disc)/(2*theta)
        v = Fs(y2**2)
        if z < 0:
            y1 = (-sigma*z - disc)/(2*theta)
            v -= Fs(y1**2)
        return exp(-z*z/2)/sqrt(2*pi) * v
    # integrate over z; split for tail accuracy
    return quad(integrand, [-inf, -8, -4, -2, 0, 2, 4, 8, inf])

def median(r, theta, sigma, mu=0):
    f = lambda x: F_VG(x, r, theta, sigma, mu) - mpf(1)/2
    lo, hi = mpf(-5), mpf(5)
    # expand
    while f(lo) > 0: lo -= 5
    while f(hi) < 0: hi += 5
    for _ in range(200):
        mid = (lo+hi)/2
        if f(mid) < 0: lo = mid
        else: hi = mid
        if hi-lo < mpf(10)**-25: break
    return (lo+hi)/2

r = 0.5; theta = 1
uB = r*exp(-mpf(2)/(3*r))
print('upper bound B:', mp.nstr(uB, 10))
for sigma in [1,3,10,30,100,300,1000,3000,10000]:
    m = median(r, theta, sigma)
    print(f'sigma={sigma:>7}  median={mp.nstr(m,12)}  uB={mp.nstr(uB,8)}  {"VIOLATION" if m>uB else ""}')
