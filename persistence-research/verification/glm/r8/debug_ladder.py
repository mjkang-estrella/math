# r8 debug_ladder.py — take the stuck 2-D ladder class of (S=10, A=27) and scan ALL
# primes < 10^6 for a region kill; report the closest misses.
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_cert2d as G

c = G.Ctx(10, 27)
rho, ML, kappa, MQ = 69977569199, 83682825624, 27894274672, 27894275208
sig = G.signature(c, rho, ML, kappa, MQ)
print("sig", sig, "v3(ML)", G.vp(ML,3), "v3(MQ)", G.vp(MQ,3), "v7(ML)", G.vp(ML,7), "v7(MQ)", G.vp(MQ,7))

best = []
n = 0
for p in G.PRIMES:
    if p > 10**6: break
    d = G.ORD10[p]
    gL, gQ = math.gcd(ML, d), math.gcd(MQ, d)
    nL, nQ = d // gL, d // gQ
    inv2 = pow(pow(2, c.t0, p), -1, p)
    alive = False
    if nL * nQ == 1:
        T = (pow(10, rho, p) + c.A * pow(10, kappa, p) + c.K) * inv2 % p
        alive = G.could(p, T, sig)
    else:
        for ggL in range(rho % gL, d, gL):
            cL = G.crt_lift(rho, ML, ggL, d)
            for ggQ in range(kappa % gQ, d, gQ):
                cQ = G.crt_lift(kappa, MQ, ggQ, d)
                T = (pow(10, ggL, p) + c.A * pow(10, ggQ, p) + c.K) * inv2 % p
                sg = G.signature(c, cL, ML*nL, cQ, MQ*nQ)
                if G.could(p, T, sg):
                    alive = True; break
            if alive: break
    n += 1
    if not alive:
        print("KILL by prime", p, "d =", d, "after scanning", n, "primes")
        break
else:
    print("no kill among primes < 10^6")
# also: loose pin
qp = min(G.q_minimum(kappa, MQ, c.qmin), 40)
print("pin_loose at qp =", qp, ":", G.pin_loose(c, sig, qp))
