"""Driver: level-1 families (Pi(n) = delta), cascade stages 0-1 + validation."""
import sys, time
sys.set_int_max_str_digits(1000000)
from math import gcd
from cascade import M0, O3_0, O7_0, build_image, stage0, stage1, O3_1, O7_1, LAM1, MU1
from vunga import Vunga
from ntlib import factorint

SMOOTH = {2, 3, 7}

def smooth_split(n):
    """If n = 2^t 3^u 7^w return (t,u,w) else None."""
    t = u = w = 0
    for p, cnt in ((2, 't'), (3, 'u'), (7, 'w')):
        while n % p == 0:
            n //= p
            if cnt == 't': t += 1
            elif cnt == 'u': u += 1
            else: w += 1
    return (t, u, w) if n == 1 else None

def members(delta, Lmax=40):
    """All n = R_L + (delta-1)10^e, L <= Lmax, with n = 2^t 3^u 7^w."""
    out = []
    R = 0
    for L in range(1, Lmax + 1):
        R = R * 10 + 1
        for e in range(L):
            n = R + (delta - 1) * 10**e
            s = smooth_split(n)
            if s:
                out.append((L, e, n, s))
    return out

if __name__ == "__main__":
    lookup = build_image()
    print()
    results = {}
    for delta in range(1, 10):
        t0 = time.time()
        t_max = Vunga((delta,) if delta > 1 else ())
        mem = members(delta, 40)
        print(f"=== delta={delta}: t_max={t_max}, members(L<=40)={len(mem)} ===")
        for (L, e, n, s) in mem[:12]:
            print(f"    n={n}  L={L} e={e}  (t,u,w)={s}")
        if len(mem) > 12: print(f"    ... {len(mem)-12} more")
        s0 = stage0(delta, t_max, lookup)
        print(f"  stage0 survivors: {len(s0)}", flush=True)
        # soundness: every member's class must be in s0
        for (L, e, n, (t, u, w)) in mem:
            cls = (L % 12, e % 12, t, (u + 2) % O3_0, w % O7_0)
            if cls not in s0:
                print(f"  *** MISSING member class {cls} for n={n} ***")
        s1 = stage1(s0, delta)
        print(f"  stage1 survivors: {len(s1)}  ({time.time()-t0:.1f}s)", flush=True)
        # soundness at stage 1
        for (L, e, n, (t, u, w)) in mem:
            cls = (L % 24, e % 24, t, (u + 2) % O3_1, w % O7_1)
            if not any(r[:5] == cls for r in s1):
                print(f"  *** MISSING stage1 class {cls} for n={n} ***")
        results[delta] = (t_max, mem, s0, s1)
    # save
    import pickle
    with open("level1_results.pkl", "wb") as f:
        pickle.dump(results, f)
    print("\nsaved level1_results.pkl")
