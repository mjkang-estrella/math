#!/usr/bin/env python3
"""
Certificate C (subagent E): level-feasibility snapshot for Theorem D.

For D = 13..26 compute
    maxs(D) = max{ s(m) : m = 2^a*3^b*5^c*7^d, dc(m) = D }   (s = decimal digit sum)

Sweep domain (coverage): if dc(m) = D then m < 10^D, so with
len(m) = len23(a,b)+c+d <= ceil(a/3)+ceil(b/2)+c+d <= (a ln2+b ln3+c ln5+d ln7)/ln5 + 7/6
(because 1/3 <= ln2/ln5, 1/2 <= ln3/ln5, 1 <= ln5/ln5, 1 <= ln7/ln5)
                     < D*ln10/ln5 + 7/6 = 1.4306766*D + 1.1667,
i.e. len(m) <= B(D) = ceil(1.4306766*D + 7/6) - 1  (B(26) = 38).
Every 7-smooth m with dc(m) in [13,26] therefore appears among the lattice points
with len(m) <= 38, which are all enumerated (exact big-int products; (a,b,c,d)
<-> m bijective). Digit sums and digit counts are computed exactly.

Empirical completeness check: an independent len-UNRESTRICTED enumeration of all
7-smooth m < 10^26 (direct product-range sweep) must give the same per-D counts.

Comparison (AM-GM cascade requirement, Theorem B2): a level-i chain element m_i
with dc(m_i) = D must have s(m_i) >= D * tau_{10-i}^{1/D}.  If maxs(D) < R(D) then
NO 7-smooth D-digit number meets the requirement: level i is infeasible at D.
  level 1 (P >= 10): R(D)  = D * tau_10^{1/D},  tau_10 = 4996238671872
  level 2 (P >= 9):  R2(D) = D * tau_9^{1/D},   tau_9  = 438939648
Infeasibility is decided by EXACT integer arithmetic:
    maxs(D) < R(D)  <=>  maxs(D)^D < D^D * tau.
"""
import json
import math
import sys
import time
from bisect import bisect_right
from pathlib import Path

sys.path.insert(0, sys.path[0])
from persistence import len23_table

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "results" / "level_feasibility.json"
TAU_JSON = ROOT / "results" / "threshold_certificates.json"

DMIN, DMAX = 13, 26


def bound_B(D):
    """Proved superset bound: dc(m) = D  =>  len(m) <= B(D)."""
    return math.ceil(1.430676558 * D + 7 / 6) - 1


POW10 = [10 ** k for k in range(45)]


def ndigits(m):
    return bisect_right(POW10, m)


def sweep(len_bound):
    """All (a,b,c,d) with len23(a,b)+c+d <= len_bound; bucket by exact dc(m)."""
    t23 = len23_table(3 * len_bound + 3, 2 * len_bound + 3)
    p5 = [5 ** i for i in range(len_bound + 1)]
    p7 = [7 ** i for i in range(len_bound + 1)]
    buckets = {D: [-1, 0, 0] for D in range(DMIN, DMAX + 1)}  # [maxs, argmax, count]
    npoints = 0
    for a in range(3 * len_bound + 1):
        pa = 2 ** a
        for b in range(2 * len_bound + 1):
            l23 = t23[a][b]
            if l23 > len_bound:
                continue
            pab = pa * 3 ** b
            rem = len_bound - l23
            for c in range(rem + 1):
                pac = pab * p5[c]
                for d in range(rem - c + 1):
                    m = pac * p7[d]
                    npoints += 1
                    dc = ndigits(m)
                    if DMIN <= dc <= DMAX:
                        s = sum(map(int, str(m)))
                        bk = buckets[dc]
                        if s > bk[0]:
                            bk[0], bk[1] = s, m
                        bk[2] += 1
    return buckets, npoints


def shell_counts():
    """Independent check: enumerate ALL 7-smooth m < 10^DMAX with no len bound,
    bucket by exact dc. Counts must match the len-restricted sweep."""
    hi = 10 ** DMAX
    counts = {D: 0 for D in range(DMIN, DMAX + 1)}
    amax = int(math.log(hi) / math.log(2)) + 2
    bmax = int(math.log(hi) / math.log(3)) + 2
    cmax = int(math.log(hi) / math.log(5)) + 2
    dmax = int(math.log(hi) / math.log(7)) + 2
    assert 2 ** amax > hi and 3 ** bmax > hi and 5 ** cmax > hi and 7 ** dmax > hi
    p2 = [2 ** i for i in range(amax + 1)]
    p3 = [3 ** i for i in range(bmax + 1)]
    p5 = [5 ** i for i in range(cmax + 1)]
    p7 = [7 ** i for i in range(dmax + 1)]
    for a in range(amax + 1):
        for b in range(bmax + 1):
            pab = p2[a] * p3[b]
            if pab >= hi:
                break
            for c in range(cmax + 1):
                pac = pab * p5[c]
                if pac >= hi:
                    break
                for d in range(dmax + 1):
                    m = pac * p7[d]
                    if m >= hi:
                        break
                    dc = ndigits(m)
                    if DMIN <= dc <= DMAX:
                        counts[dc] += 1
    return counts


def main():
    t0 = time.time()
    tau = json.loads(TAU_JSON.read_text())
    TAU10 = tau["taus"][9]["tau"]
    TAU9 = tau["taus"][8]["tau"]
    assert TAU10 == 4996238671872 and TAU9 == 438939648

    Bs = {D: bound_B(D) for D in range(DMIN, DMAX + 1)}
    BMAX = max(Bs.values())
    assert BMAX == 38, f"B(26) = {BMAX} != 38"
    print(f"[C] proven len bounds B(D): {Bs}")

    buckets, npoints = sweep(BMAX)
    print(f"[C] sweep: {npoints} lattice points with len <= {BMAX}  [{time.time()-t0:.1f}s]")

    # independent completeness check (no len restriction)
    shellc = shell_counts()
    mism = [D for D in range(DMIN, DMAX + 1) if shellc[D] != buckets[D][2]]
    print(f"[C] unrestricted-shell cross-check mismatches: {mism}  [{time.time()-t0:.1f}s]")
    assert not mism, f"coverage bound failed for D in {mism}"

    rows = []
    infeasible_R, infeasible_R2 = [], []
    for D in range(DMIN, DMAX + 1):
        maxs, argm, cnt = buckets[D]
        assert maxs >= 0 and cnt > 0
        Rf = D * TAU10 ** (1.0 / D)
        R2f = D * TAU9 ** (1.0 / D)
        infeas1 = maxs ** D < (D ** D) * TAU10      # maxs < R  (exact)
        infeas2 = maxs ** D < (D ** D) * TAU9       # maxs < R2 (exact)
        if infeas1:
            infeasible_R.append(D)
        if infeas2:
            infeasible_R2.append(D)
        rows.append({
            "D": D,
            "n_smooth_dc_D": cnt,
            "maxs": maxs,
            "argmax_m": argm,
            "max_possible_9D": 9 * D,
            "best_deficit_9D_minus_maxs": 9 * D - maxs,
            "R_level1_float": round(Rf, 4),
            "level1_feasible": not infeas1,
            "R_level2_float": round(R2f, 4),
            "level2_feasible": not infeas2,
            "argmax_is_7smooth": True,
        })
        print(f"[C] D={D:>2}: n={cnt:>6}  maxs={maxs:>3} (9D={9*D})  "
              f"R1={Rf:>8.3f} {'INFEASIBLE' if infeas1 else 'feasible'}  "
              f"R2={R2f:>8.3f} {'INFEASIBLE' if infeas2 else 'feasible'}")

    # verify each argmax is really 7-smooth with the claimed digit count/sum
    from persistence import is_7smooth
    for r in rows:
        m = r["argmax_m"]
        assert is_7smooth(m) and ndigits(m) == r["D"] \
            and sum(map(int, str(m))) == r["maxs"]

    log = {
        "certificate": "C: level-feasibility snapshot for Theorem D (D = 13..26)",
        "verifier": "subagent E (test)",
        "date": time.strftime("%Y-%m-%d %H:%M:%S"),
        "sweep_bound": "len(m) <= B(D) = ceil(1.4306766*D + 7/6) - 1; B(26) = 38",
        "sweep_points": npoints,
        "shell_crosscheck": "per-D counts equal an unrestricted len-free enumeration "
                            "of all 7-smooth m < 10^26 (0 mismatches)",
        "tau10": TAU10,
        "tau9": TAU9,
        "rows": rows,
        "level1_infeasible_D": infeasible_R,
        "level2_infeasible_D": infeasible_R2,
        "runtime_seconds": round(time.time() - t0, 2),
    }
    OUT.write_text(json.dumps(log, indent=1))
    print(f"[C] wrote {OUT}")
    print(f"[C] level-1 (P>=10) infeasible D: {infeasible_R}")
    print(f"[C] level-2 (P>=9)  infeasible D: {infeasible_R2}")


if __name__ == "__main__":
    main()
