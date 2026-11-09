import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
# r8 debug_1027.py — worklist sieve with the gen_cert2d kill set; print surviving classes.
import math, sys
sys.argv = ['x']
import gen_cert2d as G

c = G.Ctx(10, 27)
print("K", c.K, "t0", c.t0, "qmin", c.qmin)
stack = [(r, 6, k, 6) for r in range(6) for k in range(6)]
seen = set()
nc = 0
while stack:
    rho, ML, kappa, MQ = stack.pop()
    key = (rho, ML, kappa, MQ)
    if key in seen: continue
    seen.add(key)
    nc += 1
    if nc > 2_000_000:
        print("CAP"); break
    sig = G.signature(c, rho, ML, kappa, MQ)
    (a_lo, a_hi), (w_lo, w_hi) = sig
    if a_hi is not None and w_hi is not None:
        rec = G.size_solutions(c, rho, ML, kappa, MQ, a_lo, w_lo)
        if rec: print("SZ", key, rec)
        continue
    kill = G.try_kill(c, rho, ML, kappa, MQ, sig)
    if kill:
        continue
    bs = G.best_split(c, rho, ML, kappa, MQ)
    use = False
    if bs is not None:
        (surv, _k), p, nL, nQ = bs
        if surv <= 6 or surv <= 0.25 * nL * nQ:
            use = True
    if use:
        (_, p, nL, nQ) = bs
        for s in range(nL):
            cL = (rho + s * ML) % (ML * nL)
            for t in range(nQ):
                cQ = (kappa + t * MQ) % (MQ * nQ)
                stack.append((cL, ML * nL, cQ, MQ * nQ))
        continue
    # deepen (same heuristic)
    ua = a_hi is None; uw = w_hi is None
    if ua and (not uw or min(G.vp(ML,3), G.vp(MQ,3)) <= min(G.vp(ML,7), G.vp(MQ,7))):
        mult, which = 3, ("L" if G.vp(ML,3) <= G.vp(MQ,3) else "Q")
    elif uw:
        mult, which = 7, ("L" if G.vp(ML,7) <= G.vp(MQ,7) else "Q")
    else:
        mult, which = 3, "L"
    if which == "L":
        stack.append(((rho + 0*ML) % (ML*mult), ML*mult, kappa, MQ))
        stack.append(((rho + 1*ML) % (ML*mult), ML*mult, kappa, MQ))
        stack.append(((rho + 2*ML) % (ML*mult), ML*mult, kappa, MQ))
    else:
        stack.append((rho, ML, (kappa + 0*MQ) % (MQ*mult), MQ*mult))
        stack.append((rho, ML, (kappa + 1*MQ) % (MQ*mult), MQ*mult))
        stack.append((rho, ML, (kappa + 2*MQ) % (MQ*mult), MQ*mult))
    if max(ML, MQ) * mult > 10**11:
        print("would exceed: class", key, "sig", sig, "kill?", kill, "depth", nc)
        break
print("nc", nc, "seen", len(seen), "stack", len(stack))
