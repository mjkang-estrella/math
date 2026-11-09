# r7 p2_resid.py — analyze residual 3-D classes: signatures, and a much wider
# kill scan (all primes <= 50000, combo caps raised, deeper pins).
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_resid.py'

import json, math, os, sys
import importlib.util
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("p2t", os.path.join(here, "p2_twofar.py"))
T = importlib.util.module_from_spec(spec); T.__name__ = "p2t"
spec.loader.exec_module(T)

COMBO_CAP = 4096
KILL_SCAN = len(T.PORDER)   # all primes
QMIN_CAP = 80

def wide_try_kill(K, t0, qlo, rhoL, rho1, rho2, M, sig):
    for p in T.PORDER[:KILL_SCAN]:
        d = T.ORD10[p]
        if M % d == 0 and (pow(10, rhoL, p) + 9 * pow(10, rho1, p) +
                           9 * pow(10, rho2, p) + K) % p == 0:
            return ("T0", p)
    for p in T.PORDER[:KILL_SCAN]:
        d = T.ORD10[p]; g = math.gcd(M, d); n = d // g
        if n ** 3 > COMBO_CAP or n < 2: continue
        inv2t0 = pow(pow(2, t0, p), -1, p)
        o3, o7 = T.O3[p], T.O7[p]
        alive = False
        for LL in range(rhoL % g, d, g):
            pL = pow(10, LL, p)
            for Q1 in range(rho1 % g, d, g):
                p1 = 9 * pow(10, Q1, p)
                for Q2 in range(rho2 % g, d, g):
                    Tv = (pL + p1 + 9 * pow(10, Q2, p) + K) * inv2t0 % p
                    if T.could(Tv, p, sig, o3, o7):
                        alive = True; break
                if alive: break
            if alive: break
        if not alive:
            return ("prime", p, n**3)
    qmin = T.q_minimum(rho1, M, qlo)
    qe = min(qmin, QMIN_CAP)
    for base, e in ((2, qe - t0), (5, qe)):
        if e < 1: continue
        m = base ** e
        x0 = (K // 2 ** t0) % m if base == 2 else \
             K * pow(pow(2, t0, m), -1, m) % m
        o3 = T.ord_pp(3, base, e); o7 = T.ord_pp(7, base, e)
        if not T.could(x0, m, sig, o3, o7):
            return ("pin", f"{base}^{qe}")
    return None

for S in (10, 1):
    residual = json.load(open(os.path.join(here, f"residual_3d_S{S}.json")))
    K = 9 * S - 1; t0 = T.vp(K, 2); qlo = 4 if S == 1 else 3
    print(f"=== S_low={S}: {len(residual)} residual classes ===")
    nkilled = 0
    for key in residual:
        rhoL, rho1, rho2, M, ph = key
        sig = T.signature3(K, rhoL, rho1, rho2, M)
        r = wide_try_kill(K, t0, qlo, rhoL, rho1, rho2, M, sig)
        fac = f"{M} = 2^{T.vp(M,2)}·3^{T.vp(M,3)}·7^{T.vp(M,7)}"
        if r:
            nkilled += 1
            print(f"  KILLED {key[:4]} sig={sig} by {r}")
        else:
            print(f"  resists {key[:4]} sig={sig} M={fac}")
    print(f"S={S}: wide scan killed {nkilled}/{len(residual)}")
