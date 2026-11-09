"""Full driver: level-1 families, stages 0-2, soundness checks, phantom bounds."""
import sys, time, pickle
sys.set_int_max_str_digits(1000000)
from math import gcd
from cascade import (M0, M1, O3_0, O7_0, O3_1, O7_1, LAM1, MU1,
                     build_image, stage0, stage1)
from stage2 import M2, build_stage2_params, build_kw_tables, stage2, minimal_n_bound
from vunga import Vunga
from ntlib import factorint

def smooth_split(n):
    t = u = w = 0
    for p in (2, 3, 7):
        while n % p == 0:
            n //= p
            if p == 2: t += 1
            elif p == 3: u += 1
            else: w += 1
    return (t, u, w) if n == 1 else None

def members(delta, Lmax=40):
    out = []
    R = 0
    for L in range(1, Lmax + 1):
        R = R * 10 + 1
        for e in range(L):
            n = R + (delta - 1) * 10**e
            s = smooth_split(n)
            if s: out.append((L, e, n, s))
    return out

def main():
    lookup = build_image()
    params = build_stage2_params()
    print("stage-2 params:", [(pr['p'], pr['s3'], pr['s7']) for pr in params], flush=True)
    kw_tables = build_kw_tables(params)
    results = {}
    for delta in range(1, 10):
        t0 = time.time()
        t_max = Vunga((delta,) if delta > 1 else ())
        mem = members(delta, 40)
        print(f"\n=== delta={delta}: t_max={t_max}, |members(L<=40)|={len(mem)} ===", flush=True)
        s0 = stage0(delta, t_max, lookup)
        print(f"  stage0 survivors: {len(s0)}", flush=True)
        for (L, e, n, (t, u, w)) in mem:
            cls = (L % 12, e % 12, t, (u + 2) % O3_0, w % O7_0)
            if cls not in s0: print(f"  *** MISSING s0 class {cls} n={n}")
        s1 = stage1(s0, delta)
        print(f"  stage1 survivors: {len(s1)}", flush=True)
        for (L, e, n, (t, u, w)) in mem:
            cls = (L % 24, e % 24, t, (u + 2) % O3_1, w % O7_1)
            if not any(r[:5] == cls for r in s1):
                print(f"  *** MISSING s1 class {cls} n={n}")
        s2 = stage2(s1, delta, params, kw_tables)
        # soundness at stage 2
        for (L, e, n, (t, u, w)) in mem:
            U1, W1 = (u + 2) % O3_1, w % O7_1
            ku = ((u + 2) - U1) // O3_1
            kw = (w - W1) // O7_1
            found = False
            for r in s2:
                if (r['L48'] == L % 48 and r['e48'] == e % 48 and r['t'] == t
                        and r['U1'] == U1 and r['W1'] == W1
                        and ku % r['ku_mod'] == r['ku_res'] and kw % r['kw_mod'] == r['kw_res']):
                    found = True; break
            if not found:
                print(f"  *** MISSING s2 class for n={n} (ku={ku}, kw={kw})")
        print(f"  stage2 soundness: OK", flush=True)
        # phantom bound
        best = None
        for r in s2:
            n_lb, u_min, w_min = minimal_n_bound(r)
            if best is None or n_lb < best[0]: best = (n_lb, u_min, w_min, r)
        if best:
            n_lb = best[0]
            print(f"  min phantom n >= 3^{best[1]} * 7^{best[2]} * 2^{best[3]['t']}")
            print(f"  digit count of bound ~ {len(str(n_lb))-1}+ digits (exact: {len(str(n_lb))} digits)", flush=True)
        results[delta] = dict(t_max=t_max, members=mem, s0=s0, s1=s1, s2=s2, bound=best)
        print(f"  ({time.time()-t0:.1f}s total)", flush=True)
    with open("level1_full.pkl", "wb") as f:
        pickle.dump(results, f)
    print("\nsaved level1_full.pkl")

if __name__ == "__main__":
    main()
