"""Extended checks:
 1. law min nu2(ImB_{2m+1}) = 3m
 2. slice law: min nu2 ImB_{2m+1}(0,v) = 3m; [v^{m+1}] slice is 2^3m-unit
 3. coupling K = ImB - (slice diff): min nu2 >= 3m; pure coeffs [u^{m+1}],[v^{m+1}] >= 3m+1
 4. top-layer (14): [u^r]ImB_{2r-1} = 2^{4r-2}(2r-1)! * gamma_r * I_r
 5. deg B_n = ceil(n/2); ImB_{2k} = 0
 6. where is K's minimum attained (which coefficient)
"""
import sys, json
from math import comb, factorial
from fractions import Fraction
from core import (compute_AB, p_im, p_min_vp, p_degree, vp)

def sub_u0(p): return {(0, b): z for (a, b), z in p.items() if a == 0}
def sub_v0(p): return {(a, 0): z for (a, b), z in p.items() if b == 0}

def I_r(r):
    return sum(Fraction(comb(r - 1, j), 2 * j + 1) for j in range(r))

def main(N):
    A, B = compute_AB(N)
    res = {"law_ok": True, "slice_ok": True, "slice_unit_ok": True,
           "K_ok": True, "K_pure_ok": True, "top_layer_ok": True,
           "deg_ok": True, "even_ok": True, "rows": []}
    for m in range(0, (N - 1) // 2 + 1):
        n = 2 * m + 1
        im = p_im(B[n])
        r = m + 1
        # law
        mn = p_min_vp(im)
        law_ok = (mn == 3 * m)
        res["law_ok"] &= law_ok
        # slices
        Sv = sub_u0(im); Su = sub_v0(im)
        minS = p_min_vp(Sv); c = Sv.get((0, m + 1), 0)
        slice_ok = (minS == 3 * m) and (vp(c) == 3 * m)
        res["slice_ok"] &= (minS >= 3 * m)
        res["slice_unit_ok"] &= (vp(c) == 3 * m)
        # coupling
        W = {}
        for (a, b), z in Sv.items(): W[(0, b)] = W.get((0, b), 0) + z
        for (a, b), z in Su.items(): W[(a, 0)] = W.get((a, 0), 0) - z
        K = {k: im.get(k, 0) - W.get(k, 0) for k in set(im) | set(W)}
        K = {k: v for k, v in K.items() if v}
        minK = p_min_vp(K)
        ku = K.get((m + 1, 0), 0); kv = K.get((0, m + 1), 0)
        K_ok = minK >= 3 * m
        K_pure_ok = vp(ku) >= 3 * m + 1 and vp(kv) >= 3 * m + 1
        res["K_ok"] &= K_ok
        res["K_pure_ok"] &= K_pure_ok
        # top layer (14): [u^{m+1}] ImB = 2^{4r-2}(2r-1)! gamma_r I_r
        pure = im.get((m + 1, 0), 0)
        gamma = Fraction(2 * comb(2 * r, r), (2 * r - 1) * 16 ** r)
        expect = 2 ** (4 * r - 2) * factorial(2 * r - 1) * gamma * I_r(r)
        top_ok = (pure == expect)
        res["top_layer_ok"] &= top_ok
        # min attainment location of K
        minat = [k for k, v in K.items() if vp(v) == minK]
        row = dict(m=m, law=law_ok, minS=minS, slice_unit=vp(c), minK=minK,
                   K_pure=(vp(ku), vp(kv)), top=top_ok, degK=p_degree(K),
                   K_min_at=sorted(minat)[:4], nKcoeff=len(K))
        res["rows"].append(row)
        print(json.dumps(row))
    for n in range(1, N + 1):
        res["deg_ok"] &= (p_degree(B[n]) == (n + 1) // 2)
    res["even_ok"] = all(len(p_im(B[2 * k])) == 0 for k in range(1, N // 2 + 1))
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    json.dump(res, open("verification_results.json", "w"), indent=1)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 30)
