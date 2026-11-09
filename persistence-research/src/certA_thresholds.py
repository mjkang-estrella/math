#!/usr/bin/env python3
"""
Certificate A (subagent E): thresholds tau_k = min{7-smooth m : P(m) >= k}, k = 1..10.

Candidate tau_10 = 4996238671872 = 2^19 * 3^4 * 7^6 = Pi(277777788888899).

Method
------
1. Verify the candidate is 7-smooth with P == 10 exactly (two independent
   implementations: persistence() and persistence_naive()).
2. Exhaustive lattice sweep of ALL (a,b,c,d) with 2^a*3^b*5^c*7^d < tau_10.
   Float logs (a*ln2+b*ln3+c*ln5+d*ln7 < ln tau_10) are used ONLY to bound loop
   ranges (+2 slack); every boundary decision is an EXACT integer comparison.
   Unique prime factorization makes (a,b,c,d) <-> m bijective: no duplicates,
   no gaps. (0,0,0,0) -> m=1 included.
3. P evaluated exactly for every point with src/persistence.persistence and
   cross-checked against persistence_naive on 100% of the points.
4. tau_k read off in increasing-m order; the prefix {m < tau_k} must have
   max P == k-1 EXACTLY. This simultaneously certifies minimality of each tau_k
   and strict monotonicity tau_1 < tau_2 < ... < tau_10.
5. Independent completeness check: a Hamming-heap enumeration of all 7-smooth
   integers < tau_10 must reproduce the lattice point set exactly.

If the sweep ever finds max P >= 10 below the candidate, the candidate is
corrected to the offending value and the sweep is repeated (robustness loop).
"""
import heapq
import json
import math
import sys
import time
from pathlib import Path

sys.path.insert(0, sys.path[0])
from persistence import persistence, persistence_naive, is_7smooth

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "results" / "threshold_certificates.json"

TAU10_CAND = 4996238671872  # 2^19 * 3^4 * 7^6


def enumerate_lattice(bound):
    """All (m, a, b, c, d) with m = 2^a*3^b*5^c*7^d < bound (exact integer boundary)."""
    L2, L3, L5, L7 = math.log(2.0), math.log(3.0), math.log(5.0), math.log(7.0)
    lnB = math.log(bound)
    amax = int(lnB / L2) + 2
    bmax = int(lnB / L3) + 2
    cmax = int(lnB / L5) + 2
    dmax = int(lnB / L7) + 2
    # superset guards: any exponent appearing in a point with product < bound
    # must be < its max (since a single prime power already reaches the bound)
    assert 2 ** amax > bound and 3 ** bmax > bound
    assert 5 ** cmax > bound and 7 ** dmax > bound
    p2 = [2 ** i for i in range(amax + 1)]
    p3 = [3 ** i for i in range(bmax + 1)]
    p5 = [5 ** i for i in range(cmax + 1)]
    p7 = [7 ** i for i in range(dmax + 1)]
    pts = []
    for a in range(amax + 1):
        pa = p2[a]
        if pa >= bound:
            break
        for b in range(bmax + 1):
            pab = pa * p3[b]
            if pab >= bound:
                break
            for c in range(cmax + 1):
                pabc = pab * p5[c]
                if pabc >= bound:
                    break
                d = 0
                while True:
                    m = pabc * p7[d]
                    if m >= bound:
                        break
                    pts.append((m, a, b, c, d))
                    d += 1
    return pts


def hamming_all(bound):
    """Independent enumeration of every 7-smooth integer < bound (heap method)."""
    h = [1]
    seen = {1}
    out = []
    while h:
        m = heapq.heappop(h)
        out.append(m)
        for p in (2, 3, 5, 7):
            m2 = m * p
            if m2 < bound and m2 not in seen:
                seen.add(m2)
                heapq.heappush(h, m2)
    return out


def factor_expv(m):
    v = []
    for p in (2, 3, 5, 7):
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        v.append(e)
    assert m == 1
    return tuple(v)


def main():
    global TAU10_CAND
    t0 = time.time()

    # -- step 1: candidate ---------------------------------------------------
    assert is_7smooth(TAU10_CAND), "candidate not 7-smooth"
    P_cand = persistence(TAU10_CAND)
    P_cand_naive = persistence_naive(TAU10_CAND)
    assert P_cand == P_cand_naive == 10, f"P(candidate) = {P_cand} != 10"
    cand_expv = factor_expv(TAU10_CAND)
    assert cand_expv == (19, 4, 0, 6)
    print(f"[A] candidate tau_10 = {TAU10_CAND} = 2^19*3^4*7^6, P = 10 (both impls)  "
          f"[{time.time()-t0:.1f}s]")

    # -- step 2-3: exhaustive sweep with exact boundary ----------------------
    for attempt in range(5):
        pts = enumerate_lattice(TAU10_CAND)
        t_sweep = time.time()
        Pv = [persistence(m) for (m, *_r) in pts]
        Pn = [persistence_naive(m) for (m, *_r) in pts]
        assert Pv == Pn, "persistence() != persistence_naive() on sweep points"
        # independent completeness: Hamming heap must reproduce the same value set
        ham = hamming_all(TAU10_CAND)
        assert sorted(ham) == sorted(m for (m, *_r) in pts), "lattice vs Hamming mismatch"
        n_ham = len(ham)
        maxP = max(Pv)
        print(f"[A] sweep: {len(pts)} lattice points with m < {TAU10_CAND} "
              f"(Hamming check: {n_ham} values, sets equal); max P = {maxP}  "
              f"[{time.time()-t0:.1f}s]")
        if maxP < 10:
            break
        # candidate was not minimal: correct it and re-sweep
        TAU10_CAND = min(m for (m, *_r), p in zip(pts, Pv) if p >= 10)
        print(f"[A] candidate corrected to {TAU10_CAND}; re-sweeping")
    else:
        raise RuntimeError("candidate correction did not converge")

    # -- step 4: read off tau_k, verify prefix max P == k-1 ------------------
    order = sorted(range(len(pts)), key=lambda i: pts[i][0])
    ms = [pts[i][0] for i in order]
    Ps = [Pv[i] for i in order]
    n = len(ms)
    prefmax = [0] * (n + 1)
    for i in range(n):
        prefmax[i + 1] = max(prefmax[i], Ps[i])

    phist = {}
    for p in Ps:
        phist[p] = phist.get(p, 0) + 1

    taus = []
    j = 0
    ok = True
    for k in range(1, 11):
        while j < n and Ps[j] < k:
            j += 1
        if j < n:
            tau_k = ms[j]
            vec = pts[order[j]][1:]
        else:
            tau_k = TAU10_CAND
            vec = cand_expv
        if j == n and persistence(tau_k) < k:
            ok = False
        dom_size = j                      # all points with m < tau_k
        dom_maxP = prefmax[j]
        witness = ms[j - 1] if j >= 1 else None
        wvec = pts[order[j - 1]][1:] if j >= 1 else None
        wP = Ps[j - 1] if j >= 1 else None
        taus.append({
            "k": k,
            "tau": tau_k,
            "exp_vector": list(vec),
            "is_7smooth": is_7smooth(tau_k),
            "P": persistence(tau_k),
            "P_naive": persistence_naive(tau_k),
            "domain_size": dom_size,
            "domain_max_P": dom_maxP,
            "domain_max_witness": {"m": witness, "exp_vector": list(wvec) if wvec else None,
                                   "P": wP},
        })
        assert dom_maxP == k - 1, f"k={k}: prefix max P = {dom_maxP} != {k-1}"
        assert taus[-1]["P"] == k, f"k={k}: P(tau_{k}) = {taus[-1]['P']} != {k}"
        print(f"[A] tau_{k} = {tau_k:>16}  vec={vec}  P={taus[-1]['P']}  "
              f"|domain(m<tau_k)| = {dom_size:>6}  maxP(domain) = {dom_maxP}")

    # monotonicity + chain cross-checks
    vals = [t["tau"] for t in taus]
    monotone = all(vals[i] < vals[i + 1] for i in range(9))
    assert monotone, f"tau not strictly increasing: {vals}"
    from persistence import digit_product
    pi10 = digit_product(TAU10_CAND)
    chain_ok = (pi10 == taus[8]["tau"])  # Pi(tau_10) == tau_9 ?
    print(f"[A] monotone tau_1<...<tau_10: {monotone};  Pi(tau_10) = {pi10} "
          f"== tau_9: {chain_ok}  [{time.time()-t0:.1f}s]")

    expected = {"tau_9": 438939648, "tau_10": 4996238671872}
    confirmed = {"tau_9": vals[8] == 438939648, "tau_10": vals[9] == 4996238671872}
    print(f"[A] expected tau_9 = 438939648: {confirmed['tau_9']}; "
          f"tau_10 = 4996238671872: {confirmed['tau_10']}")

    log = {
        "certificate": "A: thresholds tau_k = min{7-smooth m : P(m) >= k}, k=1..10",
        "verifier": "subagent E (test)",
        "date": time.strftime("%Y-%m-%d %H:%M:%S"),
        "candidate_tau10": 4996238671872,
        "candidate_exp_vector": [19, 4, 0, 6],
        "P_candidate": 10,
        "sweep": {
            "domain": "all (a,b,c,d) with 2^a*3^b*5^c*7^d < tau_10 (exact integer "
                      "boundary; float logs used only to bound loop ranges)",
            "n_points": len(pts),
            "hamming_crosscheck_values": n_ham,
            "hamming_sets_equal": True,
            "P_impl_crosscheck": "persistence == persistence_naive on 100% of points",
            "max_P_in_domain": maxP,
            "P_histogram": {str(k): v for k, v in sorted(phist.items())},
        },
        "taus": taus,
        "monotone_strict": monotone,
        "Pi_tau10_equals_tau9": chain_ok,
        "expected_values": expected,
        "expected_confirmed": confirmed,
        "runtime_seconds": round(time.time() - t0, 2),
    }
    OUT.write_text(json.dumps(log, indent=1))
    print(f"[A] wrote {OUT}  [{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main()
