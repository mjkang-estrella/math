"""Corrected decomposition + full verification.

Theorem 1 (proved in discovery.md): B_n(v,u) = conj-coeff(B_n(u,v)); hence
ImB_n antisymmetric under u<->v, ImB_{2k}=0, and
  ImB_{2m+1}(u,v) = W_m(u,v) + K_m(u,v),
  W_m = ImB_{2m+1}(0,v) - ImB_{2m+1}(0,u)   (layer-0 / one-center difference),
  K_m = uv(u-v) R_m(u,v),  R_m in Z[u,v] symmetric  (layers r>=1).

Law (min nu2 of ImB_{2m+1} coeffs = 3m) iff
  (A) slice law: all coeffs of ImB_{2m+1}(0,v) divisible by 2^3m and
      [v^{m+1}] slice is exactly 2^3m times odd  (one-center statement), and
  (B) 2^3m | R_m  (coupling/mixed-coefficient divisibility).
"""
import sys, json
from math import comb, factorial
from fractions import Fraction
from core import (compute_AB, p_im, p_min_vp, p_degree, vp)

def sub_u0(p): return {(0, b): z for (a, b), z in p.items() if a == 0}

def divide_uvuv(K):
    """K assumed antisymmetric, vanishing on axes; return R = K/(uv(u-v)) or None."""
    # K = uv(u-v) R:  monomial (a,b) of R -> (a+2,b+1) and (a+1,b+2).
    # Recover R by descending degree.
    R = {}
    items = sorted(K.items(), key=lambda kv: -(kv[0][0] + kv[0][1]))
    for (a, b), z in items:
        # subtract contribution of already-found R terms
        pass
    # simpler: peel from the top. R has degree degK-3.
    R = {}
    ok = True
    # process monomials of K in decreasing total degree; each K coeff = R[(a-2,b-1)] - R[(a-1,b-2)]
    maxdeg = max((a + b for (a, b) in K), default=-1)
    for d in range(maxdeg, -1, -1):
        for a in range(0, d + 1):
            b = d - a
            z = K.get((a, b), 0)
            # contributions from R monomials of degree d-3: (a-2,b-1),(a-1,b-2)
            r1 = R.get((a - 2, b - 1), 0) if a >= 2 and b >= 1 else 0
            r2 = R.get((a - 1, b - 2), 0) if a >= 1 and b >= 2 else 0
            val = z - (r1 - r2)
            if val:
                if a < 1 or b < 1 or a + b < 3:
                    return None  # not divisible by uv(u-v)
                R[(a - 1, b - 1)] = val  # from uv(u-v)*[(a-1,b-1)]: produces (a,b)?
        # recompute properly below instead
    return None

def divide_uvuv2(K):
    """Direct: R[(i,j)] contributes uv(u-v)*u^i v^j = u^{i+2}v^{j+1} - u^{i+1}v^{j+2}.
    Solve triangle from low degrees."""
    R = {}
    deg = max((a + b for (a, b) in K), default=-1)
    for d in range(0, deg + 1):        # degree of K monomials
        for a in range(0, d + 1):
            b = d - a
            z = K.get((a, b), 0)
            r1 = R.get((a - 2, b - 1), 0) if (a >= 2 and b >= 1) else 0
            r2 = R.get((a - 1, b - 2), 0) if (a >= 1 and b >= 2) else 0
            val = z - (r1 - r2)
            if val != 0:
                if a < 2 or b < 1:
                    return None
                R[(a - 2, b - 1)] = val
    # verify
    for (a, b), z in K.items():
        s = 0
        if (a - 2, b - 1) in R: s += R[(a - 2, b - 1)]
        if (a - 1, b - 2) in R: s -= R[(a - 1, b - 2)]
        if s != z: return None
    return R

def main(N):
    A, B = compute_AB(N)
    res = {"law_ok": True, "slice_div_ok": True, "slice_unit_ok": True,
           "R_ok": True, "R_sym_ok": True, "R_integral_ok": True,
           "top_layer_ok": True, "deg_ok": True, "even_ok": True,
           "K_axis_ok": True, "rows": []}
    for m in range(0, (N - 1) // 2 + 1):
        n = 2 * m + 1
        im = p_im(B[n])
        mn = p_min_vp(im)
        res["law_ok"] &= (mn == 3 * m)
        Sv = sub_u0(im)                       # ImB(0,v): {(0,b): coeff}
        # W(u,v) = ImB(0,v) - ImB(0,u);  ImB(0,u) has coeffs {(a,0): Sv[(0,a)]}
        W = {}
        for (a, b), z in Sv.items(): W[(0, b)] = W.get((0, b), 0) + z
        for (a, b), z in Sv.items(): W[(b, 0)] = W.get((b, 0), 0) - z
        K = {k: im.get(k, 0) - W.get(k, 0) for k in set(im) | set(W)}
        K = {k: v for k, v in K.items() if v}
        # K vanishes on axes?
        res["K_axis_ok"] &= all((a >= 1 and b >= 1) for (a, b) in K)
        minK = p_min_vp(K)
        R = divide_uvuv2(K)
        if R is None:
            res["R_integral_ok"] = False
            Rmin = None
        else:
            Rmin = p_min_vp(R)
            res["R_ok"] &= (Rmin >= 3 * m)
            res["R_sym_ok"] &= all(R.get((b, a), 0) == z for (a, b), z in R.items())
        minS = p_min_vp(Sv)
        c = Sv.get((0, m + 1), 0)
        res["slice_div_ok"] &= (minS >= 3 * m)
        res["slice_unit_ok"] &= (vp(c) == 3 * m)
        # top layer (14)
        r = m + 1
        pure = im.get((m + 1, 0), 0)
        gamma = Fraction(2 * comb(2 * r, r), (2 * r - 1) * 16 ** r)
        Ir = sum(Fraction(comb(r - 1, j), 2 * j + 1) for j in range(r))
        res["top_layer_ok"] &= (pure == 2 ** (4 * r - 2) * factorial(2 * r - 1) * gamma * Ir)
        row = dict(m=m, law=(mn == 3 * m), minS=minS, unit=vp(c),
                   minK=minK, Rmin=Rmin, degK=p_degree(K), degR=p_degree(R) if R else None)
        res["rows"].append(row)
        print(json.dumps(row))
    res["deg_ok"] = all(p_degree(B[n]) == (n + 1) // 2 for n in range(1, N + 1))
    res["even_ok"] = all(len(p_im(B[2 * k])) == 0 for k in range(1, N // 2 + 1))
    print(json.dumps({k: v for k, v in res.items() if k != "rows"}))
    json.dump(res, open("verification_results.json", "w"), indent=1)

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 30)
