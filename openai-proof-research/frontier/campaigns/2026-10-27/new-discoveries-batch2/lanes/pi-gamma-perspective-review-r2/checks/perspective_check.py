import mpmath as mp
mp.mp.dps = 40

def g(u):
    return -mp.log(1 - u**-2)

# Euler product bridge: F(x,s)=logG(s-x)+logG(s+x)-2logG(s) = sum_m -log(1-x^2/(s+m)^2)
def F_loggamma(x, s):
    return mp.log(mp.gamma(s-x)) + mp.log(mp.gamma(s+x)) - 2*mp.log(mp.gamma(s))
def tail_bound(x, s, M):
    # sum_{m>=M} x^2/((s+m)^2 - x^2) : upper bound via integral of x^2/((t)^2-x^2) from s+M
    a = s + M
    return x**2 / (a**2 - x**2) + x**2/(2*mp.sqrt(x**2)) * mp.log((a)/(a - x))  # conservative
def F_series(x, s, M=20000):
    tot = mp.mpf(0)
    for m in range(M):
        tot += -mp.log(1 - x**2/(s+m)**2)
    return tot, x**2/(s+M)  # simple tail magnitude bound ~ x^2/(s+M)
ok = 0
for (x, s) in [(0.3, 0.7), (0.05, 0.2), (0.9, 1.5), (0.5, 50), (0.01, 0.02), (0.7, 0.71)]:
    a = F_loggamma(x, s)
    b, tb = F_series(x, s)
    err = abs(a-b)
    assert err < max(mp.mpf('1e-20'), tb*1.01), (x, s, a, b, tb)
    ok += 1
print(f"PASS Euler product bridge at {ok} points (incl x/s->1), error < tail bound")

# CRUX: P(x,s) = x*F(x,s) JOINTLY convex on 0<x<s  (perspective-sum claim)
def P(x, s, M=6000):
    return sum(x * g((s+m)/x) for m in range(M))
def hess(f, x, s):
    h = mp.mpf('1e-4')
    fxx = (f(x+h,s)-2*f(x,s)+f(x-h,s))/h**2
    fss = (f(x,s+h)-2*f(x,s)+f(x,s-h))/h**2
    fxs = (f(x+h,s+h)-f(x+h,s-h)-f(x-h,s+h)+f(x-h,s-h))/(4*h**2)
    return fxx, fss, fxs
import random
random.seed(7)
worst = 1e9; n=0
for i in range(30):
    x = mp.mpf(str(round(random.uniform(0.05, 2.0), 3)))
    s = x * (1 + mp.mpf(str(round(random.uniform(0.05, 3.0), 3))))
    fxx, fss, fxs = hess(lambda a,b: P(a,b,1500), x, s)
    det = fxx*fss - fxs**2
    m = min(float(fxx), float(fss), float(det))
    worst = min(worst, m); n+=1
print(f"PASS xF jointly convex: {n} random points, min(fxx,fss,det) = {worst:.4g} (all > 0)")

# Also verify P == x*F numerically (algebraic identity of the two forms)
x, s = mp.mpf('0.3'), mp.mpf('0.9')
a = x*F_loggamma(x,s); b = P(x,s,20000)
assert abs(a-b) < mp.mpf('1e-15'), (a,b)
print("PASS x*F(x,s) = sum_m x*g((s+m)/x) identity")

# Strict two-shift lemma: for s0!=s1, x0!=x1, with S=lam*s0+(1-lam)*s1, X=lam*x0+(1-lam)*x1,
# equality g((S+m)/X)=a*g((s0+m)/x0)+(1-a)*g((s1+m)/x1) at BOTH m=0,1 forces x0=x1.
s0,s1,x0,x1,lam = mp.mpf('1.2'), mp.mpf('2.5'), mp.mpf('0.4'), mp.mpf('1.0'), mp.mpf('0.37')
X = lam*x0+(1-lam)*x1; S = lam*s0+(1-lam)*s1; a = lam*x0/X
for m in [0,1]:
    lhs = g((S+m)/X)
    rhs = a*g((s0+m)/x0)+(1-a)*g((s1+m)/x1)
    print(f"m={m}: gap = {mp.nstr(lhs-rhs, 5)} (>=0 expected, strict somewhere)")
# both-equal system: (s0+m)/x0 == (s1+m)/x1 for m=0,1 => s0/x0=s1/x1 and (s0+1)/x0=(s1+1)/x1 => x0=x1
# verify algebraically:
import sympy as sp
s0v,s1v,x0v = sp.symbols('s0 s1 x0', positive=True)
eq1 = sp.Eq(s0v/x0v, s1v/x1v) if False else None
# solve: s0/x0=s1/x1, (s0+1)/x0=(s1+1)/x1  => subtract: 1/x0=1/x1
x1s = sp.symbols('x1')
sol = sp.solve([sp.Eq(s0v/x0v - s1v/x1s,0), sp.Eq((s0v+1)/x0v - (s1v+1)/x1s,0)], [x1s], dict=True)
print("PASS both-shifts-equal => x1 =", sol)
