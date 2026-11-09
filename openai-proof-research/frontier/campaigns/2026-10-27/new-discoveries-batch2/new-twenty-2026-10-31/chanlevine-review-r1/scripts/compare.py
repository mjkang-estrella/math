"""Compare the brute-force counts (tier 1: Definition 5.2 terminal SCCs; tier 2: Lemma 5.3(iii) greedy)
with (a) each other, (b) Conjecture 8.3, (c) the closed formula of 338887-proof.md (re-implemented here
from the TEXT of the proof, lines 28-38), (d) the intermediate claims of Steps 1 and 6: for every
e | n and a primitive e-th root zeta, W_m(zeta) = sum_i N(i) zeta^i is a rational integer, vanishes
unless e | m, and equals w_{n,m}(e); computed exactly in Z[z]/Phi_e, and (e) Table 8.1 of the source.
Usage: python3 -I compare.py OUT.json file1.json [file2.json ...]
"""
import json
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyclo import Cyc  # noqa: E402

TABLE_8_1 = {  # source arXiv:1804.03322v2, Table 8.1 (r(C_{n,n,i}), i = 0..n-1)
    3: [26, 24, 24],
    4: [122, 120, 118, 120],
    5: [642, 640, 640, 640, 640],
    6: [3630, 3624, 3624, 3630, 3624, 3624],
    7: [21394, 21392, 21392, 21392, 21392, 21392, 21392],
    8: [130090, 130080, 130072, 130080, 130086, 130080, 130072, 130080],
}


def qe(e):
    if e % 2:
        return 0
    return 2 if e % 4 == 0 else -2


def ipoly_mul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] += x * y
    return r


def ipoly_sub(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]


def lucas_V(e, r):
    """V_r as integer polynomial in T = t^e: V_0 = 2, V_1 = p, V_j = p V_{j-1} - (1-T)^2 V_{j-2}."""
    p = [2, qe(e)]
    d = [1, -2, 1]
    V = [[2], p]
    for j in range(2, r + 1):
        V.append(ipoly_sub(ipoly_mul(p, V[j - 1]), ipoly_mul(d, V[j - 2])))
    return V[r]


def w_formula(n, m, e):
    """Coefficient of t^m in V_{n/e}(t^e)/(1-t^e)^{n/e} - 2 (m >= 1)."""
    if m % e:
        return 0
    r = n // e
    M = m // e
    V = lucas_V(e, r)
    s = 0
    for a, c in enumerate(V):
        if a <= M:
            s += c * math.comb(M - a + r - 1, r - 1)
    return s - (2 if m == 0 else 0)


def mobius(k):
    res, p, x = 1, 2, k
    while p * p <= x:
        if x % p == 0:
            x //= p
            if x % p == 0:
                return 0
            res = -res
        p += 1
    if x > 1:
        res = -res
    return res


def ramanujan(e, i):
    g0 = math.gcd(e, i)
    return sum(mobius(e // g) * g for g in range(1, g0 + 1) if g0 % g == 0)


def formula_N(n, m):
    d = math.gcd(n, m)
    out = []
    for i in range(n):
        s = sum(w_formula(n, m, e) * ramanujan(e, i) for e in range(1, d + 1) if d % e == 0)
        out.append(Fraction(s, n))
    return out


def W_exact(N, n, e):
    """sum_i N(i) zeta^i for zeta a primitive e-th root (e | n, so zeta^n = 1), computed modulo Phi_e."""
    acc = Cyc.const(e, 0)
    for i, c in enumerate(N):
        acc = acc + Cyc.const(e, c) * Cyc.zpow(e, i % e)
    return acc


def main():
    out = sys.argv[1]
    data = {}
    for fn in sys.argv[2:]:
        with open(fn) as f:
            d = json.load(f)
        rows = d["results"] if isinstance(d, dict) else d
        tier = "greedy" if isinstance(d, dict) else ("def_L%d" % rows[0]["L"])
        for row in rows:
            data.setdefault((row["n"], row["m"]), {})[tier] = row["r"]
    report = {"cases": 0, "tier_disagreements": [], "conjecture_failures": [], "formula_mismatches": [],
              "W_not_integer": [], "W_nonzero_e_not_dividing_m": [], "W_vs_w_mismatch": [],
              "table_8_1": {}, "tiers_present": {}}
    for (n, m), tiers in sorted(data.items()):
        report["cases"] += 1
        vals = list(tiers.values())
        for t in tiers:
            report["tiers_present"][t] = report["tiers_present"].get(t, 0) + 1
        if any(v != vals[0] for v in vals):
            report["tier_disagreements"].append([n, m, tiers])
        N = vals[0]
        groups = {}
        for i in range(n):
            groups.setdefault(math.gcd(math.gcd(n, m), i), set()).add(N[i])
        if any(len(s) > 1 for s in groups.values()):
            report["conjecture_failures"].append([n, m, N])
        F = formula_N(n, m)
        if any(f.denominator != 1 for f in F) or [int(f) for f in F] != N:
            report["formula_mismatches"].append([n, m, N, [str(f) for f in F]])
        for e in range(1, n + 1):
            if n % e:
                continue
            W = W_exact(N, n, e)
            wi = W.as_int()
            if wi is None:
                report["W_not_integer"].append([n, m, e])
                continue
            if m % e and wi != 0:
                report["W_nonzero_e_not_dividing_m"].append([n, m, e, wi])
            if wi != w_formula(n, m, e):
                report["W_vs_w_mismatch"].append([n, m, e, wi, w_formula(n, m, e)])
        if m == n and n in TABLE_8_1:
            report["table_8_1"][str(n)] = {"brute": N, "source": TABLE_8_1[n], "match": N == TABLE_8_1[n]}
    report["all_ok"] = (not report["tier_disagreements"] and not report["conjecture_failures"]
                        and not report["formula_mismatches"] and not report["W_not_integer"]
                        and not report["W_nonzero_e_not_dividing_m"] and not report["W_vs_w_mismatch"]
                        and len(report["table_8_1"]) == 6
                        and all(v["match"] for v in report["table_8_1"].values()))
    print(json.dumps(report, indent=1))
    with open(out, "w") as f:
        json.dump(report, f, indent=1)


if __name__ == "__main__":
    main()
