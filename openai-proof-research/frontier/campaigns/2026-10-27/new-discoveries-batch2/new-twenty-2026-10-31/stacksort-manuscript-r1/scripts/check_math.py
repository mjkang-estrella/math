#!/usr/bin/env python3
"""Independent diagnostic checks for the manuscript (NOT a proof; no Lean).

Usage: python3 -I scripts/check_math.py <frozen P table json> <StackSortCertificate.lean>
        <StackSortControls.lean> <out json> <NMAX recursion>
Written from the paper's mathematics in this lane; imports nothing from other lanes.
"""
import itertools, json, math, re, sys, time
from collections import defaultdict
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 80
T0 = time.time()


def s(w):
    if not w:
        return ()
    m = max(w); i = w.index(m)
    return s(w[:i]) + s(w[i + 1:]) + (m,)


def brute(nmax):
    P, maxfib, fam = {}, {}, {}
    for n in range(1, nmax + 1):
        cnt = defaultdict(int)
        for w in itertools.permutations(range(1, n + 1)):
            cnt[s(w)] += 1
        P[n] = sum(v * v for v in cnt.values())
        maxfib[n] = max(cnt.values())
        # 2^(n-1) family: F_1={1}, F_n = {n p, p n}
        F = {(1,)}
        for k in range(2, n + 1):
            F = {(k,) + p for p in F} | {p + (k,) for p in F}
        fam[n] = (len(F), all(s(p) == tuple(range(1, n + 1)) for p in F))
    return P, maxfib, fam


def compositions(M, r):
    for cuts in itertools.combinations(range(1, M), r - 1):
        yield (0,) + cuts + (M,)


def tuple_lemmas(Mmax):
    """Literal tuple counts XI, II, MF(maximum-final) for M <= Mmax; check T1, T3/T4 formulas."""
    XI, II, MF = {}, {}, {}
    for M in range(1, Mmax + 1):
        groups = defaultdict(list)  # output -> list of (r, internal boundary set)
        for w in itertools.permutations(range(1, M + 1)):
            for r in range(1, M + 1):
                for c in compositions(M, r):
                    words = [w[c[j]:c[j + 1]] for j in range(r)]
                    out = sum((s(x) for x in words), ())
                    # boundaries are output positions c[1..r-1] (sorting preserves word lengths)
                    groups[out].append((r, frozenset(c[1:-1])))
        for out, lst in groups.items():
            mf = out[-1] == M
            agg = defaultdict(int)
            for r, b in lst:
                agg[(r, b)] += 1
            items = list(agg.items())
            for (r1, b1), n1 in items:
                for (r2, b2), n2 in items:
                    k = (M, r1, r2)
                    XI[k] = XI.get(k, 0) + n1 * n2
                    if not (b1 & b2):
                        II[k] = II.get(k, 0) + n1 * n2
                    if mf:
                        MF[k] = MF.get(k, 0) + n1 * n2
    X = lambda M, r, t: (1 if (r == 0 and t == 0) else 0) if M == 0 else XI.get((M, r, t), 0)
    I = lambda M, r, t: 0 if M == 0 else II.get((M, r, t), 0)
    mu = (1, 2, 1)
    res = {'T1_common_cut': True, 'T2_irreducible_max_final': True, 'T3_deletion': True, 'T4_fixed_max': True,
           'cases': 0}
    for M in range(1, Mmax + 1):
        for r in range(1, M + 1):
            for t in range(1, M + 1):
                res['cases'] += 1
                conv = lambda fixed: sum((math.comb(M - 1, b - 1) if fixed else math.comb(M, b)) *
                                         X(M - b, r - a, t - c) * I(b, a, c)
                                         for b in range(1, M) for a in range(1, r) for c in range(1, t))
                if X(M, r, t) != I(M, r, t) + conv(False):
                    res['T1_common_cut'] = False
                dele = sum(mu[x] * mu[y] * X(M - 1, r - 1 + x, t - 1 + y) for x in range(3) for y in range(3))
                if MF.get((M, r, t), 0) != dele:
                    res['T3_deletion'] = False
                if MF.get((M, r, t), 0) != I(M, r, t) + conv(True):
                    res['T4_fixed_max'] = False
    # T2: every irreducible pair is maximum-final -> II <= MF and (MF - II) = reducible max-final, checked via T4
    for k, v in II.items():
        if v > MF.get(k, 0):
            res['T2_irreducible_max_final'] = False
    res['XI_M_1_1_equals_II_M_1_1'] = all(XI[(M, 1, 1)] == II[(M, 1, 1)] for M in range(1, Mmax + 1))
    res['Mmax'] = Mmax
    return res


def topmax(N):
    """Top-max recursion, pruned to arities r,s <= min(M, N+1-M)."""
    X = {(0, 0, 0): 1}; I = {}
    mu = (1, 2, 1)
    def gx(M, r, t): return X.get((M, r, t), 0)
    def gi(M, r, t): return I.get((M, r, t), 0)
    for M in range(1, N + 1):
        B = min(M, N + 1 - M)
        for r in range(1, B + 1):
            for t in range(1, B + 1):
                dele = sum(mu[x] * mu[y] * gx(M - 1, r - 1 + x, t - 1 + y) for x in range(3) for y in range(3))
                cf = cx = 0
                for b in range(1, M):
                    conv = 0
                    for a in range(1, min(r, b + 1)):
                        for c in range(1, min(t, b + 1)):
                            iv = I.get((b, a, c))
                            if iv:
                                xv = X.get((M - b, r - a, t - c))
                                if xv:
                                    conv += xv * iv
                    if conv:
                        cf += math.comb(M - 1, b - 1) * conv
                        cx += math.comb(M, b) * conv
                ii = dele - cf
                assert ii >= 0
                I[(M, r, t)] = ii
                X[(M, r, t)] = ii + cx
    return {n: X[(n, 1, 1)] for n in range(1, N + 1)}


def lower_G(P, seeds, nmax):
    G = {0: 1}
    for n in range(1, nmax + 1):
        if n <= seeds:
            G[n] = P[n]
        else:
            G[n] = 4 * G[n - 1] + sum(math.comb(n - 1, i) * G[i] * G[n - 1 - i] for i in range(1, n - 1))
    return G


def doubling_passes(Pa, a, num=173, den=100):
    # (d_a / (4(a+1)))^(1/(a+1)) > num/den  <=>  Pa * den^(a+1) > 4 (a+1) a! num^(a+1)
    return Pa * den ** (a + 1) > 4 * (a + 1) * math.factorial(a) * num ** (a + 1)


def droot(x, k):
    return float((Decimal(x).ln() / k).exp())


def main():
    tab_path, cert_path, ctrl_path, out_path, nrec = sys.argv[1:6]
    nrec = int(nrec)
    raw = json.load(open(tab_path))
    P = {int(k): int(v) for k, v in raw.items()}
    R = {'note': 'diagnostic only; not a proof', 'frozen_table_n_range': [min(P), max(P)]}
    bp, mf, fam = brute(8)
    R['brute_P_1_8_match_table'] = all(bp[n] == P[n] for n in bp)
    R['brute_P'] = bp
    cat = lambda n: math.comb(2 * n, n) // (n + 1)
    R['max_fibre_equals_catalan_n_le_8'] = all(mf[n] == cat(n) for n in mf)
    R['family_2pow_n_minus_1_sorts_to_identity_n_le_8'] = all(fam[n] == (2 ** (n - 1), True) for n in fam)
    R['tuple_lemmas'] = tuple_lemmas(6)
    t1 = time.time(); tm = topmax(nrec)
    R['topmax_recursion_N'] = nrec
    R['topmax_matches_table'] = all(tm[n] == P[n] for n in tm)
    R['topmax_seconds'] = round(time.time() - t1, 2)
    R['root_split_holds_2_to_82'] = all(
        4 * P[n - 1] + sum(math.comb(n - 1, i) * P[i] * P[n - 1 - i] for i in range(1, n - 1)) <= P[n]
        for n in range(2, max(P) + 1))
    R['doubling_holds_all_2a_plus_1_le_81'] = all(math.comb(2 * a, a) * P[a] ** 2 <= P[2 * a + 1]
                                                   for a in range(1, (max(P) - 1) // 2 + 1))
    lean_lower = int(re.search(r'def lower130 : ℕ := (\d+)', open(cert_path, encoding='utf-8').read()).group(1))
    lean_l129 = int(re.search(r'def lower129 : ℕ := (\d+)', open(ctrl_path, encoding='utf-8').read()).group(1))
    G20 = lower_G(P, 20, 130)
    R['G130_equals_lean_lower130'] = G20[130] == lean_lower
    R['G129_equals_lean_lower129'] = G20[129] == lean_l129
    R['certificate130_holds'] = 4 * 131 * math.factorial(130) * 173 ** 131 < lean_lower * 100 ** 131
    R['control_base129_fails'] = not (4 * 130 * math.factorial(129) * 173 ** 130 < lean_l129 * 100 ** 130)
    R['control_threshold195_fails'] = lean_lower * 100 ** 131 <= 4 * 131 * math.factorial(130) * 195 ** 131
    R['G130_over_P130_unknown'] = 'P_130 not computed; G_130 <= P_130 is the proved inequality'
    R['G130_doubling_bound'] = droot(Fraction(lean_lower, 4 * 131 * math.factorial(130)) * 1, 131) if False else \
        float((Decimal(lean_lower) / Decimal(4 * 131 * math.factorial(130))).ln().__truediv__(131).exp())
    R['subsequence_first_terms'] = [131 * 2 ** k - 1 for k in range(5)]
    first = {}
    for seeds, amax in ((20, 300), (16, 300), (14, 600), (13, 1000)):
        G = lower_G(P, seeds, amax)
        first[seeds] = next((a for a in range(seeds + 1, amax + 1) if doubling_passes(G[a], a)), None)
    R['first_a_passing_1_73_by_seed_depth'] = first
    G13 = lower_G(P, 13, 910)
    R['seeds13_a910_certificate'] = doubling_passes(G13[910], 910)
    R['seeds13_a909_fails'] = not doubling_passes(G13[909], 909)
    passes = [a for a in range(1, max(P) + 1) if doubling_passes(P[a], a)]
    R['exact_table_first_a_passing_1_73'] = passes[0]
    R['exact_table_all_a_50_to_82_pass_1_73'] = passes == list(range(50, max(P) + 1))
    R['exact_a82_bound_gt_1_8047'] = doubling_passes(P[82], 82, 18047, 10000)
    R['exact_a82_bound_lt_1_8048'] = not doubling_passes(P[82], 82, 18048, 10000)
    R['exact_a82_bound_gt_1_80468'] = doubling_passes(P[82], 82, 180468, 100000)
    R['exact_a82_bound_lt_1_80469'] = not doubling_passes(P[82], 82, 180469, 100000)
    R['exact_a82_bound_gt_1_8046'] = doubling_passes(P[82], 82, 18046, 10000)
    R['exact_a50_bound_gt_1_7330'] = doubling_passes(P[50], 50, 17330, 10000)
    # heuristic only: Richardson-type fit r_n = L + A/n + B/n^2 through n = 80, 81, 82 of d_n/d_(n-1)
    rr = {n: Fraction(P[n], n * P[n - 1]) for n in (80, 81, 82)}
    import itertools as _it
    # solve 3x3 linear system exactly
    rowsA = [[Fraction(1), Fraction(1, n), Fraction(1, n * n)] for n in (80, 81, 82)]
    bvec = [rr[n] for n in (80, 81, 82)]
    def det(m):
        return (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
                + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    D = det(rowsA)
    Lm = [[bvec[i]] + rowsA[i][1:] for i in range(3)]
    R['heuristic_ratio_extrapolation_L'] = float(det(Lm) / D)
    R['v1v2_remark_a_passing_1_8'] = [a for a in range(1, max(P) + 1) if doubling_passes(P[a], a, 9, 5)]
    sup_first = next(n for n in range(8, max(P) + 2) if P[n - 1] * 100 ** n > n * n * math.factorial(n - 1) * 173 ** n)
    R['sup_formula_first_n_passing_1_73'] = sup_first
    rows = {}
    for n in sorted(set(list(range(1, 21)) + [25, 30, 40, 50, 60, 70, 78, 79, 80, 81, 82])):
        d = Decimal(P[n]) / Decimal(math.factorial(n))
        rows[n] = {'P': str(P[n]), 'digits': len(str(P[n])),
                   'root': float((d.ln() / n).exp()),
                   'ratio': float(d / (Decimal(P[n - 1]) / Decimal(math.factorial(n - 1)))) if n > 1 else None,
                   'doubling_bound': float(((d / (4 * (n + 1))).ln() / (n + 1)).exp()),
                   'sup_bound_n_plus_1': float(((d / ((n + 1) ** 2))).ln().__truediv__(n + 1).exp()) if n + 1 >= 8 else None}
    R['rows'] = rows
    R['seconds'] = round(time.time() - T0, 2)
    json.dump(R, open(out_path, 'w'), indent=1)
    short = {k: v for k, v in R.items() if k not in ('rows', 'brute_P')}
    print(json.dumps(short, indent=1))


if __name__ == '__main__':
    main()
