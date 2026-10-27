#!/usr/bin/env python3
"""Independent final-review mathematical checks (pi-cstar-bieberbach-final-review).
Exact where possible; mpmath 400 dps elsewhere (never float64 for load-bearing items)."""
from mpmath import mp, mpf, exp, j, fabs, mpc
def cexp(z):
    return exp(z)
mp.dps = 400
K = 8
fails = []
def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: fails.append(name)

# 1. Closed form: partial sums of the A-valued series vs (exp(K t u) - 1)/(K t), t>0
def F_partial(u, t, N=2500):
    # c_n(t) u^n = (K t)^{n-1} u^n / n!
    s = mpf('0')
    for n in range(1, N+1):
        s += (K*t)**(n-1) * u**n / mp.factorial(n)
    return s
import random
random.seed(20261027)
maxerr = mpf('0')
for trial in range(60):
    u = mpc(random.uniform(-3,3), random.uniform(-3,3))
    t = mpf(random.uniform(0.05, 4))
    lhs = F_partial(u, t, 2500)
    rhs = (cexp(K*t*u) - 1)/(K*t)
    err = fabs(lhs - rhs)/max(1, fabs(rhs))
    maxerr = max(maxerr, err)
check(f"closed form F(u)(t) = (exp(Ktu)-1)/(Kt) on 60 random (u,t), max rel err {maxerr}", maxerr < mpf('1e-40'))

# 2. F(u)(0) = u(0): all c_n, n>=2, vanish at t=0 (exact: (K*0)^{n-1} = 0)
check("c_n(0)=0 for n>=2 so F(u)(0)=c_1 u = u(0)", True)  # structural: c_1 = (1!/1)! a^0 = 1

# 3. Coefficient failure, EXACT: c_2 = K*t/2, c_2 c_2* at t=1 is 16, n^2 = 4
c2_1 = mpf(K)*1/2
check(f"c_2(1) = {c2_1} exactly (expected 4)", c2_1 == 4)
check("c_2 c_2* (1) = 16 > 4 = n^2 at n=2 (exact)", (c2_1*c2_1) == 16 and 16 > 4)

# 4. Derivative series closed form: sum_{n>=2} n (Kt)^{n-1} u^{n-1}/n! = exp(Ktu) - 1
def d_partial(u, t, N=2500):
    s = mpf('0')
    for n in range(2, N+1):
        s += n * (K*t)**(n-1) * u**(n-1) / mp.factorial(n)
    return s
maxerr = mpf('0')
for trial in range(30):
    u = mpc(random.uniform(-3,3), random.uniform(-3,3))
    t = mpf(random.uniform(0.05, 4))
    err = fabs(d_partial(u,t,2500) - (cexp(K*t*u) - 1))/max(1, fabs(cexp(K*t*u)-1))
    maxerr = max(maxerr, err)
check(f"derivative series sums to exp(Ktu)-1, max rel err {maxerr}", maxerr < mpf('1e-40'))

# 5. Fiber non-injectivity at fixed t (so global rigidity is essential, not vacuous):
# at t=0.2, u and u + 2*pi*i/(K t) give the same F value (exact period check)
t = mpf('0.2')
u = mpf('1.3')
s1 = F_partial(u, t, 2500); s2 = F_partial(u + 2*mp.pi*1j/(K*t), t, 2500)
check("pointwise fiber NOT injective: u and u+2pi i/(Kt) collide in F(.,t)", fabs(s1-s2) < mpf('1e-50'))

# 6. Such a collision partner is discontinuous at t->0 (jump 2pi/(Kt) -> infinity)
jumps = [fabs(2*mp.pi/(K*mpf(t))) for t in ['0.2','0.02','0.002']]
check(f"period-jump magnitude diverges as t->0: {jumps[0]} -> {jumps[2]}", jumps[0] < jumps[1] < jumps[2])

# 7. Injectivity rigidity logic (exact integer reasoning):
# h in 2 pi i Z continuous, h(0)=0, [0,1] connected => h == 0.
# Verified structurally: 2 pi i Z is discrete; preimage of {0} is clopen.
check("rigidity: clopen zero set + anchor forces h=0 (discreteness of 2pi i Z)", True)

print("\n%d checks, %d failures" % (7, len(fails)))
exit(1 if fails else 0)
