#!/usr/bin/env python3
"""Independent reviewer code (rlmexc-review-r1).  Written from the source
definitions (AJC 86(3) p.388), NOT from the discovery lane's scripts.

Usage: python3 -I rlm_poly.py N OUTJSON

Enumerates all of S_N (one-line notation, 1-based values), and for every k with
1 <= k <= N computes the signed sum
    P_{N,k} = sum_{pi in S_N, min(type(pi)) >= k} (-1)^inv(pi) x_{RLMv(pi)} y_{EXCv(pi)}
exactly (integer coefficients, monomials keyed by (sorted RLMv, sorted EXCv)).
Reports, for the VoR normalisation F_{N,k} = (-1)^(N-1) P_{N,k} and for the raw
(arXiv/MathDB) P_{N,k}, the number of positive and negative coefficients, and the
coefficient of x_R y_E with R = {1, N-4, N-2, N-1}, E = [N] minus R (when N >= 5).
Also runs source-data sanity checks (Theorem 1.0.1 for k = 2; the S_7 example
table; the single-cycle term counts against A124302; the printed "(23)" polynomial).
"""
import itertools
import json
import sys


def excv(p):
    # p is a tuple of values p[0..n-1] = pi(1..n)
    return frozenset(p[j] for j in range(len(p)) if p[j] > j + 1)


def exci(p):
    return frozenset(j + 1 for j in range(len(p)) if p[j] > j + 1)


def rlmi(p):
    n = len(p)
    out = []
    cur = n + 1  # minimum of the suffix strictly to the right
    for i in range(n - 1, -1, -1):
        if p[i] < cur:
            out.append(i + 1)
            cur = p[i]
    return frozenset(out)


def rlmv(p):
    return frozenset(p[i - 1] for i in rlmi(p))


def rlmv_bruteforce(p):
    n = len(p)
    return frozenset(p[i] for i in range(n) if all(p[i] < p[j] for j in range(i + 1, n)))


def inv(p):
    n = len(p)
    return sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j])


def cycle_type(p):
    n = len(p)
    seen = [False] * (n + 1)
    lens = []
    for s in range(1, n + 1):
        if not seen[s]:
            L = 0
            x = s
            while not seen[x]:
                seen[x] = True
                x = p[x - 1]
                L += 1
            lens.append(L)
    return tuple(sorted(lens, reverse=True))  # fixed points are parts equal to 1


def mono_key(R, E):
    return (tuple(sorted(R)), tuple(sorted(E)))


def key_str(k):
    R, E = k
    return "x" + ",".join(map(str, R)) + "|y" + ",".join(map(str, E))


def main():
    n = int(sys.argv[1])
    out = sys.argv[2]
    # contrib[(mono, mincycle)] = signed count
    contrib = {}
    single_cycle = {}  # unsigned sum over type (n)
    nperm = 0
    for p in itertools.permutations(range(1, n + 1)):
        nperm += 1
        s = -1 if inv(p) % 2 else 1
        ct = cycle_type(p)
        m = mono_key(rlmv(p), excv(p))
        kk = (m, ct[-1])
        contrib[kk] = contrib.get(kk, 0) + s
        if ct == (n,):
            single_cycle[m] = single_cycle.get(m, 0) + 1
    res = {"n": n, "permutations_enumerated": nperm, "per_k": {}}
    R = E = None
    if n >= 5:
        Rs = {1, n - 4, n - 2, n - 1}
        Es = set(range(1, n + 1)) - Rs
        target = mono_key(Rs, Es)
        res["target_monomial"] = key_str(target)
    for k in range(1, n + 1):
        P = {}
        for (m, mc), c in contrib.items():
            if mc >= k:
                P[m] = P.get(m, 0) + c
        P = {m: c for m, c in P.items() if c != 0}
        sgn = (-1) ** (n - 1)
        F = {m: sgn * c for m, c in P.items()}
        d = {
            "raw_terms": len(P),
            "raw_pos": sum(1 for c in P.values() if c > 0),
            "raw_neg": sum(1 for c in P.values() if c < 0),
            "vor_pos": sum(1 for c in F.values() if c > 0),
            "vor_neg": sum(1 for c in F.values() if c < 0),
            "vor_negative_monomials": sorted(
                [[key_str(m), c] for m, c in F.items() if c < 0])[:40],
        }
        if n >= 5:
            d["target_raw_coeff"] = P.get(target, 0)
            d["target_vor_coeff"] = F.get(target, 0)
        if k == 2:
            # Theorem 1.0.1: F_{n,2} = sum_{j=1}^{n-1} x_1..x_j y_{j+1}..y_n
            expect = {mono_key(set(range(1, j + 1)), set(range(j + 1, n + 1))): 1
                      for j in range(1, n)}
            d["theorem_1_0_1_matches"] = (F == expect)
        res["per_k"][str(k)] = d
    res["single_cycle_distinct_terms"] = len(single_cycle)
    res["single_cycle_total"] = sum(single_cycle.values())
    if n == 4:
        res["single_cycle_poly_n4"] = sorted([[key_str(m), c] for m, c in single_cycle.items()])
    # sanity: RLM fast vs brute force on a sample, and the S_7 example table
    chk = True
    for idx, p in enumerate(itertools.permutations(range(1, n + 1))):
        if idx % 97 == 0 and rlmv(p) != rlmv_bruteforce(p):
            chk = False
    res["rlmv_fast_equals_bruteforce_sample"] = chk
    if n == 7:
        table = {"2135764": (5, {1, 4, 5}, {2, 3, 7}, {1, 3, 4}),
                 "2153746": (5, {1, 3, 5}, {2, 4, 6, 7}, {1, 3, 4, 6}),
                 "6713245": (11, {1, 2}, {3, 5, 6, 7}, {1, 2, 4, 5})}
        ok = {}
        for w, (iv, ei, ri, rv) in table.items():
            p = tuple(int(ch) for ch in w)
            ok[w] = (inv(p) == iv and exci(p) == ei and rlmi(p) == ri and rlmv(p) == rv)
        res["source_S7_example_table_matches"] = ok
    with open(out, "w") as f:
        json.dump(res, f, indent=1, sort_keys=True)
    summary = {k: (v["vor_pos"], v["vor_neg"], v["raw_pos"], v["raw_neg"],
                   v.get("target_vor_coeff"), v.get("theorem_1_0_1_matches"))
               for k, v in res["per_k"].items()}
    print("n", n, "perms", nperm)
    print("k: (vor_pos, vor_neg, raw_pos, raw_neg, target_vor_coeff, thm101)")
    for k, v in summary.items():
        print(" ", k, v)
    print("single-cycle distinct terms", res["single_cycle_distinct_terms"])
    for key in ("source_S7_example_table_matches", "rlmv_fast_equals_bruteforce_sample",
                "single_cycle_poly_n4"):
        if key in res:
            print(key, res[key])


if __name__ == "__main__":
    main()
