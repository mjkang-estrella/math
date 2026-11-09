"""Independent exact verification for MathDB 378395 (reviewer code, written from scratch).

Usage: python3 -I verify_facet.py LEAN_FILE OUT_JSON

Checks, with exact rational arithmetic (fractions.Fraction):
  1. the functional l from PROOF.md (re-typed here) equals the one in the Lean module;
  2. l(col(i,j,k)) >= 0 for all 80 cells of a 4 x 4 x 5 table;
  3. rank of all columns = 44 and rank of the tight columns = 43, so F = cone(tight columns)
     is a facet (span F = span of tight columns because F is the cone over them);
  4. the five k-slices have pairwise distinct zero patterns;
  5. for every state map s3 : [5] -> [4] (all 1024) and every assignment of the size-5 axis
     to a target axis (also covering variable permutations), two cells in one fibre differ
     in membership in F;
  6. extra (informative): row and column patterns, i.e. whether F is collapsible along the
     first or second variable to some smaller (non-(4,4,4)) table;
  7. sanity of the rank code: dim P^{p,q,r} = pq+pr+qr-p-q-r+1 for the sizes of source Table 1;
  8. the 43 cells `bcell` of the Lean module are tight and independent.
"""
import itertools
import json
import re
import sys
from fractions import Fraction


def rank(rows):
    m = [[Fraction(x) for x in r] for r in rows]
    rk = 0
    ncol = len(m[0]) if m else 0
    for c in range(ncol):
        piv = None
        for r in range(rk, len(m)):
            if m[r][c] != 0:
                piv = r
                break
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for r in range(len(m)):
            if r != rk and m[r][c] != 0:
                f = m[r][c] / m[rk][c]
                m[r] = [x - f * y for x, y in zip(m[r], m[rk])]
        rk += 1
    return rk


def column(p, q, r, i, j, k):
    v = [0] * (p * q + p * r + q * r)
    v[i * q + j] = 1
    v[p * q + i * r + k] = 1
    v[p * q + p * r + j * r + k] = 1
    return v


A = [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 0]]
B = [[0, 0, 0, 0, 0], [-1, 0, 0, 0, 0], [-1, -1, -1, 0, 0], [0, -1, 0, -1, 0]]
C = [[1, 1, 1, 1, 0], [1, 1, 1, 0, 0], [1, 0, 0, 0, 0], [0, 1, 0, 1, 0]]
P, Q, Rr = 4, 4, 5


def parse_lean_ell(path):
    txt = open(path, encoding="utf-8").read()
    m = re.search(r"def ellZ[^=]*:=\s*wt(.*?)theorem ell_nonneg", txt, re.S)
    nums = [int(x) for x in re.findall(r"-?\d+", m.group(1))]
    a = [nums[4 * i:4 * i + 4] for i in range(4)]
    rest = nums[16:]
    b = [rest[5 * i:5 * i + 5] for i in range(4)]
    rest = rest[20:]
    c = [rest[5 * i:5 * i + 5] for i in range(4)]
    bc = re.search(r"def bcell[^=]*:=\s*!\[(.*?)\]", txt, re.S).group(1)
    cells = [tuple(int(x) for x in t) for t in re.findall(r"\((\d), (\d), (\d)\)", bc)]
    return a, b, c, cells


def main():
    lean_path, out = sys.argv[1], sys.argv[2]
    res = {}
    la, lb, lc, bcell = parse_lean_ell(lean_path)
    res["lean_ell_equals_proofmd"] = (la, lb, lc) == (A, B, C)

    w = {(i, j, k): A[i][j] + B[i][k] + C[j][k]
         for i in range(P) for j in range(Q) for k in range(Rr)}
    res["min_weight"] = min(w.values())
    res["nonneg_all_80"] = all(v >= 0 for v in w.values()) and len(w) == 80
    tight = [c for c, v in w.items() if v == 0]
    res["n_tight"] = len(tight)
    allcols = [column(P, Q, Rr, *c) for c in w]
    res["rank_all_columns"] = rank(allcols)
    res["rank_tight_columns"] = rank([column(P, Q, Rr, *c) for c in tight])
    res["source_dim_formula_445"] = P * Q + P * Rr + Q * Rr - P - Q - Rr + 1
    res["is_facet"] = (res["nonneg_all_80"] and res["rank_tight_columns"] + 1 == res["rank_all_columns"]
                       and len(tight) < 80)

    def pat_k(k):
        return tuple(w[(i, j, k)] == 0 for i in range(P) for j in range(Q))

    def pat_i(i):
        return tuple(w[(i, j, k)] == 0 for j in range(Q) for k in range(Rr))

    def pat_j(j):
        return tuple(w[(i, j, k)] == 0 for i in range(P) for k in range(Rr))

    res["slice_k_patterns_distinct"] = len({pat_k(k) for k in range(Rr)}) == Rr
    res["slice_i_patterns_distinct"] = len({pat_i(i) for i in range(P)}) == P
    res["slice_j_patterns_distinct"] = len({pat_j(j) for j in range(Q)}) == Q
    res["slices_k_zero_counts"] = [sum(pat_k(k)) for k in range(Rr)]
    res["weights_by_k"] = [[[w[(i, j, k)] for j in range(Q)] for i in range(P)] for k in range(Rr)]

    # 5. every s3 : [5] -> [4]; the fibre of (i, j, k) and (i, j, l) coincide when s3 k = s3 l,
    # whatever s1, s2 and whatever target axis receives variable 3.
    failures = 0
    for s3 in itertools.product(range(4), repeat=5):
        pairs = [(k, l) for k in range(5) for l in range(k + 1, 5) if s3[k] == s3[l]]
        assert pairs, "pigeonhole"
        ok = any(any((w[(i, j, k)] == 0) != (w[(i, j, l)] == 0) for i in range(P) for j in range(Q))
                 for k, l in pairs)
        failures += 0 if ok else 1
    res["state_maps_s3_checked"] = 4 ** 5
    res["state_maps_s3_without_witness"] = failures

    # 7. rank-code sanity: dims of source Table 1
    dims = {}
    for (p, q, r, d) in [(2, 2, 2, 7), (2, 2, 3, 10), (2, 2, 4, 13), (2, 3, 3, 14), (2, 3, 4, 18),
                         (3, 3, 3, 19), (3, 3, 4, 24), (3, 3, 5, 29), (3, 4, 4, 30), (4, 4, 4, 37),
                         (4, 4, 5, 44)]:
        rk = rank([column(p, q, r, i, j, k) for i in range(p) for j in range(q) for k in range(r)])
        dims[f"{p}x{q}x{r}"] = [rk, d, rk == d]
    res["dim_sanity"] = dims

    # 8. the Lean basis cells
    res["lean_bcell_count"] = len(bcell)
    res["lean_bcell_all_tight"] = all(w[c] == 0 for c in bcell)
    res["lean_bcell_rank"] = rank([column(P, Q, Rr, *c) for c in bcell])
    res["lean_c0_weight"] = w[(0, 0, 0)]

    # negative control: perturb one coefficient and show the certificate breaks
    B2 = [row[:] for row in B]
    B2[1][0] = -2
    w2 = {(i, j, k): A[i][j] + B2[i][k] + C[j][k] for i in range(P) for j in range(Q) for k in range(Rr)}
    res["negative_control_perturbed_b10_min_weight"] = min(w2.values())

    json.dump(res, open(out, "w"), indent=1)
    keys = ["lean_ell_equals_proofmd", "nonneg_all_80", "n_tight", "rank_all_columns",
            "rank_tight_columns", "is_facet", "slice_k_patterns_distinct", "slice_i_patterns_distinct",
            "slice_j_patterns_distinct", "state_maps_s3_without_witness", "lean_bcell_all_tight",
            "lean_bcell_rank", "negative_control_perturbed_b10_min_weight"]
    for k in keys:
        print(k, res[k])
    print("dim_sanity_all_ok", all(v[2] for v in dims.values()))


if __name__ == "__main__":
    main()
