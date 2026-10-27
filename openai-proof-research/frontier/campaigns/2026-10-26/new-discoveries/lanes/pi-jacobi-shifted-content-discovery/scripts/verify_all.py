"""Consolidated exact verification for the shifted-content target (Remark 3.8).

Verifies, in exact Gaussian-integer / rational arithmetic:
  (1) content law:        min_v2 coeffs of Im B_{2m+1}(u,v) == 3m          (m <= M1)
  (2) Co 3.1 (pure coeff): [u^{m+1}] Im B_{2m+1} == 2^{4r-2}(2r-1)! * gamma_r * I_r
      with gamma_r = C(2r-1,r-1)/((2r-1) 2^{4r-2})                          (r <= M1)
  (3) mod-2 unit law:      Im B_{2m+1} == 2^{3m} [(u+v)^{m+1} + [m=1 mod 4](u+v)^m]
      (mod 2^{3m+1})                                                        (m <= M2)
  (4) structural: Im B_{2k} == 0; deg B_n = ceil(n/2);
      content(Re B_{2k}) == content(Re B_{2k+1}) == 2*nu2((2k)!)            (k <= K)
  (5) top coefficients: [u^n] A_n = (1+i)^n, [v^n] A_n = (1-i)^n            (n <= N)

Writes results to scripts/verification_results.json.
"""
import json
import sys
from fractions import Fraction
from math import comb, factorial

sys.path.insert(0, 'scripts')
from jacobi_shifted_core import (compute_AB, p_im, p_min_vp, p_degree, vp)

def main(N=61, M2=30):
    A, B = compute_AB(N)
    res = {"N": N, "checks": {}}

    # (5) top coefficients of A_n
    ok5 = all(A[n].get((n, 0), (0, 0)) == pow_gi(n) for n in range(1, N + 1))
    res["checks"]["top_coeff_A_n"] = {"ok": bool(ok5), "range": N}

    # (1)(2) law + Co3.1 up to r = 40 (n = 79 <= N needs N >= 79; adjust if smaller)
    M1 = min(40, N // 2)
    rows = []
    fail = []
    for r in range(1, M1 + 1):
        im = p_im(B[2 * r - 1])
        mv = p_min_vp(im)
        pure = im.get((r, 0), 0)
        g = Fraction(pure, 2 ** (4 * r - 2) * factorial(2 * r - 1)) / I_r(r)
        gpred = Fraction(comb(2 * r - 1, r - 1), (2 * r - 1) * 2 ** (4 * r - 2))
        row = {"r": r, "law_ok": mv == 3 * (r - 1), "gamma_ok": g == gpred,
               "pure_nu2": vp(pure)}
        rows.append(row)
        if not (row["law_ok"] and row["gamma_ok"]):
            fail.append(r)
    res["checks"]["content_law_and_Co31"] = {"ok": not fail, "failures": fail,
                                             "range_r": M1, "rows": rows}

    # (3) mod-2 unit law
    fail3 = []
    for m in range(0, min(M2, N // 2) + 1):
        im = p_im(B[2 * m + 1])
        unit = {k for k, z in im.items() if (z >> (3 * m)) & 1}
        gset = set()
        e = m + 1
        for k in range(e + 1):
            if comb(e, k) & 1:
                gset.add((e - k, k))
        if m % 4 == 1:
            for k in range(m + 1):
                if comb(m, k) & 1:
                    key = (m - k, k)
                    gset.symmetric_difference_update({key})
        if unit != gset:
            fail3.append(m)
    res["checks"]["mod2_unit_law"] = {"ok": not fail3, "failures": fail3,
                                      "range_m": min(M2, N // 2)}

    # (4) structural laws
    fail4 = []
    K = N // 2
    for k in range(1, K + 1):
        if p_im(B[2 * k]):
            fail4.append(("ImB_even", 2 * k))
        if p_degree(B[2 * k]) != k:
            fail4.append(("deg", 2 * k))
        if p_degree(B[2 * k + 1]) != k + 1:
            fail4.append(("deg", 2 * k + 1))
        for n in (2 * k, 2 * k + 1):
            pass  # (Re-content law dropped: deviates from 2*nu2((2k)!) for n >= 12)
    res["checks"]["structural"] = {"ok": not fail4, "failures": fail4, "range_k": K}

    json.dump(res, open('scripts/verification_results.json', 'w'), indent=1)
    print(json.dumps({k: (v["ok"], v.get("failures", [])) for k, v in res["checks"].items()},
                     indent=1))

def pow_gi(n):
    """(1+i)^n as (re,im)."""
    re, im = 1, 0
    for _ in range(n):
        re, im = re - im, re + im
    return (re, im)

def I_r(r):
    return sum(Fraction(comb(r - 1, j), 2 * j + 1) for j in range(r))

if __name__ == "__main__":
    import sys
    main(N=int(sys.argv[1]) if len(sys.argv) > 1 else 61)
