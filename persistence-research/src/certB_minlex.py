#!/usr/bin/env python3
"""
Certificate B (subagent E): Theorem C.2 closed-form min-lex minimal factorizations
F(a,b) of 2^a*3^b, for ALL 0 <= a <= 240, 0 <= b <= 160  (241*161 = 38,801 pairs).

For every pair we verify:
  (i)   len(F) == len23(a,b)            [src/persistence.py len23_table / len_of_smooth]
  (ii)  product of digits of F == 2^a*3^b   [exact exponent bookkeeping + big-int spot checks]
  (iii) F is lex-minimal among ALL minimal-length factorizations:
        - prescribed LOCAL SEARCH: every replacement of r in {2,3} digits of F by
          s <= r digits with the same product (s = r: length-preserving; s < r:
          length-reducing, must not exist) is enumerated exhaustively; none may
          yield a lex-smaller sorted multiset. Iterated to a fixpoint.
        - independent GLOBAL check: an exact greedy lex-min construction
          (maximize #2s, then #3s, then #4s, ...; exchange argument: among
          equal-length factorizations of the same value, more 2s => lex-smaller)
          must reproduce F exactly.
        - GROUND TRUTH: full enumeration of all minimal-length factorizations by
          pruned DFS on a<=36, b<=24, plus 40 random pairs over the whole range
          via an independent complete parametrized enumeration; lex-min must
          equal F there too.

The len23 DP itself is validated: bracketing len23 >= max(ceil(a/3), ceil(b/2))
and len23 <= ceil(a/3)+ceil(b/2) on all 38,801 pairs, plus exact DFS minimum on
the small range.
"""
import json
import random
import sys
import time
from collections import Counter
from math import ceil
from pathlib import Path

sys.path.insert(0, sys.path[0])
from persistence import len23_table, len_of_smooth

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "results" / "minlex_certificates.json"

AMAX, BMAX = 240, 160
DIG6 = (2, 3, 4, 6, 8, 9)
E2 = {2: 1, 3: 0, 4: 2, 6: 1, 8: 3, 9: 0}
E3 = {2: 0, 3: 1, 4: 0, 6: 1, 8: 0, 9: 2}


# ---------------------------------------------------------------------------
# Theorem C.2 closed form
# ---------------------------------------------------------------------------
def closed_form_F(a, b):
    r3, r2 = a % 3, b % 2
    if r3 == 0 and r2 == 0:
        return (8,) * (a // 3) + (9,) * (b // 2)
    if r3 == 1 and r2 == 0:
        return (2,) + (8,) * ((a - 1) // 3) + (9,) * (b // 2)
    if r3 == 2 and r2 == 0:
        return (4,) + (8,) * ((a - 2) // 3) + (9,) * (b // 2)
    if r3 == 0 and r2 == 1:
        return (3,) + (8,) * (a // 3) + (9,) * ((b - 1) // 2)
    if r3 == 1 and r2 == 1:
        return (6,) + (8,) * ((a - 1) // 3) + (9,) * ((b - 1) // 2)
    return (2, 6) + (8,) * ((a - 2) // 3) + (9,) * ((b - 1) // 2)


# ---------------------------------------------------------------------------
# local-search machinery (prescribed certificate)
# ---------------------------------------------------------------------------
def submultisets(cur, r):
    """All sub-multisets R of cur with |R| = r, as sorted tuples (deduped)."""
    cnt = Counter(cur)
    digits = sorted(cnt)
    out = set()

    def rec(i, rem, acc):
        if i == len(digits):
            if rem == 0:
                out.add(tuple(sorted(acc)))
            return
        d = digits[i]
        for c in range(min(cnt[d], rem) + 1):
            rec(i + 1, rem - c, acc + [d] * c)

    rec(0, r, [])
    return sorted(out)


def replacements(x, y, s):
    """All sorted tuples of s digits from {2,3,4,6,8,9} with 2-exponent x, 3-exponent y."""
    out = []

    def rec(i, rx, ry, slots, acc):
        if rx == 0 and ry == 0 and slots == 0:
            out.append(tuple(sorted(acc)))
            return
        if i == 6 or slots <= 0 or rx < 0 or ry < 0:
            return
        d = DIG6[i]
        dx, dy = E2[d], E3[d]
        maxn = slots
        if dx:
            maxn = min(maxn, rx // dx)
        if dy:
            maxn = min(maxn, ry // dy)
        for n in range(maxn + 1):
            rec(i + 1, rx - dx * n, ry - dy * n, slots - n, acc + [d] * n)

    rec(0, x, y, s, [])
    return out


def local_search(F, max_iters=1000):
    """Repeatedly apply every 2<->2, 3<->2, 3<->3 (and shorter) same-product
    replacement; return (fixpoint, n_lex_improvements_found, n_shorter_found).
    Certificate holds iff no improvement exists from F (fixpoint == F)."""
    cur = tuple(sorted(F))
    n_lex = n_short = 0
    for _ in range(max_iters):
        found = None
        base = Counter(cur)
        for r in (2, 3):
            for R in submultisets(cur, r):
                x = sum(E2[d] for d in R)
                y = sum(E3[d] for d in R)
                for s in range(1, r + 1):
                    for S in replacements(x, y, s):
                        if S == R:
                            continue  # identity
                        new = tuple(sorted(list((base - Counter(R)).elements()) + list(S)))
                        if s < r:
                            n_short += 1
                            found = new  # length-reducing: contradicts len23; apply & continue
                            break
                        if new < cur:
                            n_lex += 1
                            found = new
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found is None:
            return cur, n_lex, n_short
        cur = found
    raise RuntimeError("local search did not reach fixpoint")


# ---------------------------------------------------------------------------
# exact greedy lex-min (global certificate)
# ---------------------------------------------------------------------------
def solution_from(n2, n8, n9, a, b, L):
    """Forced completion of (n2,n8,n9) for a length-L factorization of 2^a*3^b.
    Each formula rearranges one defining equation; ALL equations re-verified."""
    n4 = L - b - n2 - n8 + n9          # from (len) minus (3-exp): n2+n4+n8-n9 = L-b
    n6 = a - n2 - 3 * n8 - 2 * n4      # rearranged 2-exp equation
    n3 = b - 2 * n9 - n6               # rearranged 3-exp equation
    if min(n2, n3, n4, n6, n8, n9) < 0:
        return None
    if n2 + n3 + n4 + n6 + n8 + n9 != L:
        return None
    if n2 + 2 * n4 + 3 * n8 + n6 != a:
        return None
    if n3 + 2 * n9 + n6 != b:
        return None
    return (n2, n3, n4, n6, n8, n9)


def greedy_lexmin(a, b, L):
    """Lex-minimal minimal-length factorization as a count vector (n2,n3,n4,n6,n8,n9):
    maximize n2; then n3 (== maximize n8); then n4 (== maximize n9).
    Necessary ranges for (n8, n9) at pinned n2 are used to prune; every candidate
    is verified by solution_from, so correctness never relies on the pruning."""
    if a == 0 and b == 0:
        return (0, 0, 0, 0, 0, 0)

    def n8_range(v2):
        # necessary: n3 = 2L-a-b-v2+n8 >= 0  and  3*n8 <= a-v2
        return max(0, a + b + v2 - 2 * L), (a - v2) // 3

    def n9_range(v2, v8):
        # necessary: n4 = L-b-v2-v8+n9 >= 0 ; n6 = a+2b-2L+v2-v8-2n9 >= 0
        return max(0, b + v2 + v8 - L), (a + 2 * b - 2 * L + v2 - v8) // 2

    def find(v2=None, v8=None, v9=None, want_max_n2=False):
        n2s = (range(min(a, L), -1, -1) if want_max_n2 else range(0, min(a, L) + 1)) \
            if v2 is None else [v2]
        for v2_ in n2s:
            lo8, hi8 = n8_range(v2_)
            n8s = range(hi8, lo8 - 1, -1) if v8 is None else [v8]
            for n8_ in n8s:
                lo9, hi9 = n9_range(v2_, n8_)
                n9s = range(hi9, lo9 - 1, -1) if v9 is None else [v9]
                for n9_ in n9s:
                    v = solution_from(v2_, n8_, n9_, a, b, L)
                    if v:
                        return v
        return None

    v = find(want_max_n2=True)                    # step 1: max n2
    if v is None:
        return None
    v2 = v[0]
    v = find(v2=v2)                               # step 2: max n3 == max n8
    if v is None:
        return None
    v8 = v[4]
    v = find(v2=v2, v8=v8)                        # step 3: max n4 == max n9
    return v


def counts_to_multiset(v):
    n2, n3, n4, n6, n8, n9 = v
    return tuple(sorted([2] * n2 + [3] * n3 + [4] * n4 + [6] * n6 + [8] * n8 + [9] * n9))


# ---------------------------------------------------------------------------
# ground-truth enumerators (independent of the parametrizations above)
# ---------------------------------------------------------------------------
def all_factorizations_dfs(a, b, L):
    """ALL multisets of exactly L digits from {2,3,4,6,8,9} with product 2^a*3^b.
    Pruned DFS over digit-type counts; prunes are necessary conditions only."""
    suf_x = [0] * 8
    suf_y = [0] * 8
    for i in range(5, -1, -1):
        suf_x[i] = max(suf_x[i + 1], E2[DIG6[i]])
        suf_y[i] = max(suf_y[i + 1], E3[DIG6[i]])
    out = []

    def rec(i, ra, rb, slots, acc):
        if ra == 0 and rb == 0 and slots == 0:
            out.append(tuple(sorted(acc)))
            return
        if i == 6 or slots <= 0:
            return
        if ra > suf_x[i] * slots or rb > suf_y[i] * slots:
            return
        if suf_x[i] and ceil(ra / suf_x[i]) > slots:
            return
        if suf_y[i] and ceil(rb / suf_y[i]) > slots:
            return
        d = DIG6[i]
        dx, dy = E2[d], E3[d]
        maxn = slots
        if dx:
            maxn = min(maxn, ra // dx)
        if dy:
            maxn = min(maxn, rb // dy)
        for n in range(maxn + 1):
            rec(i + 1, ra - dx * n, rb - dy * n, slots - n, acc + [d] * n)

    rec(0, a, b, L, [])
    return out


def all_solutions_param(a, b, L):
    """Complete enumeration of length-L factorizations via the (n8,n9,n2) box +
    airtight per-candidate verification. Used for random large-range spot checks."""
    out = []
    for n8 in range(a // 3 + 1):
        for n9 in range(b // 2 + 1):
            for n2 in range(0, min(a, L) + 1):
                v = solution_from(n2, n8, n9, a, b, L)
                if v:
                    out.append(v)
    return out


# ---------------------------------------------------------------------------
def main():
    t0 = time.time()
    t23 = len23_table(AMAX, BMAX)

    # -- DP sanity: bracketing on all pairs ----------------------------------
    bad_bracket = []
    for a in range(AMAX + 1):
        for b in range(BMAX + 1):
            v = t23[a][b]
            if not (max(ceil(a / 3), ceil(b / 2)) <= v <= ceil(a / 3) + ceil(b / 2)):
                bad_bracket.append((a, b, v))
    print(f"[B] len23 bracketing violations: {len(bad_bracket)}  [{time.time()-t0:.1f}s]")
    assert not bad_bracket

    # -- exact small-range len23 + lex-min ground truth -----------------------
    SA, SB = 36, 24
    len_bad = []
    lex_bad_small = []
    for a in range(SA + 1):
        for b in range(SB + 1):
            true_len = None
            for L in range(max(ceil(a / 3), ceil(b / 2), 1 if (a or b) else 0),
                           ceil(a / 3) + ceil(b / 2) + 1):
                if all_factorizations_dfs(a, b, L):
                    true_len = L
                    break
            true_len = true_len or 0
            if true_len != t23[a][b]:
                len_bad.append((a, b, t23[a][b], true_len))
                continue
            if (a, b) != (0, 0):
                mn = min(all_factorizations_dfs(a, b, true_len))
                F = closed_form_F(a, b)
                if tuple(sorted(F)) != mn:
                    lex_bad_small.append((a, b, tuple(sorted(F)), mn))
    print(f"[B] DFS ground truth a<={SA},b<={SB}: len23 mismatches {len(len_bad)}, "
          f"lex-min mismatches {len(lex_bad_small)}  [{time.time()-t0:.1f}s]")
    assert not len_bad and not lex_bad_small

    # -- main loop over all 38,801 pairs --------------------------------------
    n_pairs = 0
    fail_len, fail_prod, fail_lex_local, fail_lex_global = [], [], [], []
    n_shorter_total = 0
    for a in range(AMAX + 1):
        for b in range(BMAX + 1):
            n_pairs += 1
            F = closed_form_F(a, b)
            L = t23[a][b]
            # (i) length
            if len(F) != L or len_of_smooth(a, b, 0, 0, t23) != L:
                fail_len.append((a, b, len(F), L))
                continue
            # (ii) product (exact exponent bookkeeping; big-int spot check below)
            x = sum(E2[d] for d in F)
            y = sum(E3[d] for d in F)
            if (x, y) != (a, b):
                fail_prod.append((a, b, x, y))
                continue
            # (iii-a) prescribed local search to fixpoint
            fix, n_lex, n_short = local_search(F)
            n_shorter_total += n_short
            if fix != tuple(sorted(F)) or n_lex or n_short:
                fail_lex_local.append((a, b, tuple(sorted(F)), fix, n_lex, n_short))
                continue
            # (iii-b) independent global greedy lex-min
            G = greedy_lexmin(a, b, L)
            if G is None or counts_to_multiset(G) != tuple(sorted(F)):
                fail_lex_global.append((a, b, G))
        if a % 40 == 0:
            print(f"[B] ... a = {a} done  [{time.time()-t0:.1f}s]")

    print(f"[B] main loop: {n_pairs} pairs; fails: len={len(fail_len)} "
          f"prod={len(fail_prod)} lex-local={len(fail_lex_local)} "
          f"lex-global={len(fail_lex_global)}  [{time.time()-t0:.1f}s]")

    # -- big-int product spot checks ------------------------------------------
    rng = random.Random(20261019)
    spots = [(19, 4)] + [(rng.randrange(AMAX + 1), rng.randrange(BMAX + 1)) for _ in range(200)]
    prod_bad = []
    for a, b in spots:
        F = closed_form_F(a, b)
        pr = 1
        for d in F:
            pr *= d
        if pr != 2 ** a * 3 ** b:
            prod_bad.append((a, b))
    print(f"[B] big-int product spot checks: {len(spots)} pairs, {len(prod_bad)} bad")

    # -- random large-range lex-min ground truth (complete parametrized enum) --
    rng = random.Random(777)
    rand_bad = []
    for _ in range(40):
        a = rng.randrange(AMAX + 1)
        b = rng.randrange(BMAX + 1)
        L = t23[a][b]
        sols = all_solutions_param(a, b, L)
        if not sols:
            rand_bad.append((a, b, "no solution at DP length"))
            continue
        mn = counts_to_multiset(min(
            sols, key=lambda v: counts_to_multiset(v)))
        F = tuple(sorted(closed_form_F(a, b)))
        if F != mn:
            rand_bad.append((a, b, F, mn))
    print(f"[B] random large-range ground truth: 40 pairs, {len(rand_bad)} bad  "
          f"[{time.time()-t0:.1f}s]")
    assert not rand_bad

    # -- record-holder consistency: F(19,4) + {7^6} ----------------------------
    F194 = closed_form_F(19, 4)
    record_ok = F194 == (2, 8, 8, 8, 8, 8, 8, 9, 9)
    print(f"[B] F(19,4) = {F194} (record digits {2,7,7,7,7,7,7,8,8,8,8,8,8,9,9} "
          f"minus 7^6): {record_ok}")
    assert record_ok

    examples = {}
    for (a, b) in [(0, 0), (3, 0), (4, 0), (5, 0), (0, 1), (4, 1), (5, 1),
                   (19, 4), (240, 160), (239, 159), (1, 1), (2, 1)]:
        examples[f"({a},{b})"] = list(closed_form_F(a, b))

    log = {
        "certificate": "B: Theorem C.2 closed-form min-lex minimal factorizations F(a,b)",
        "verifier": "subagent E (test)",
        "date": time.strftime("%Y-%m-%d %H:%M:%S"),
        "range": {"a_max": AMAX, "b_max": BMAX, "n_pairs": n_pairs},
        "checks": {
            "length_equals_len23": {"failures": len(fail_len)},
            "product_equals_2a3b": {"failures": len(fail_prod),
                                    "bigint_spot_checks": len(spots),
                                    "bigint_failures": len(prod_bad)},
            "lex_minimality_local_search": {
                "method": "every 2<->2, 3<->2, 3<->3 (and shorter) same-product "
                          "replacement enumerated; fixpoint must equal F",
                "failures": len(fail_lex_local),
                "length_reducing_replacements_found": n_shorter_total,
            },
            "lex_minimality_global_greedy": {"failures": len(fail_lex_global)},
        },
        "counterexamples": fail_len + fail_prod + fail_lex_local + fail_lex_global,
        "validation": {
            "len23_bracket_all_pairs": "0 violations",
            "dfs_ground_truth_range": f"a<={SA}, b<={SB}",
            "dfs_len23_mismatches": len(len_bad),
            "dfs_lexmin_mismatches": len(lex_bad_small),
            "random_complete_enumeration_pairs": 40,
            "random_mismatches": len(rand_bad),
        },
        "record_consistency_F_19_4": record_ok,
        "examples": examples,
        "runtime_seconds": round(time.time() - t0, 2),
    }
    OUT.write_text(json.dumps(log, indent=1))
    print(f"[B] wrote {OUT}  [{time.time()-t0:.1f}s]")

    if fail_len or fail_prod or fail_lex_local or fail_lex_global or prod_bad:
        print("[B] VERDICT: FAILED — see counterexamples")
        sys.exit(1)
    print("[B] VERDICT: CERTIFIED — Theorem C.2 holds for all 38,801 pairs")


if __name__ == "__main__":
    main()
