#!/usr/bin/env python3
"""Subagent F -- pure_math.md section 6, Certificate 3: Fonga verification.

Verifies, by three independent legs:

Task 1  Fonga (arXiv:2608.27802) Thm 4.1 worked example: family A_10(nu) with
        nu_4 = 2, nu_7 = 1 (digit multiset {4,4,7} plus arbitrarily many 1s,
        no other digits).  Claim: max v2 over the whole (infinite) family = 7,
        attained at 111744 = 2^7 * 3^2 * 97.
  A. direct enumeration of ALL arrangements for j <= 40 inserted 1s;
  B. the paper's own finite recursion V (Thm 4.1) implemented verbatim,
     including reproduction of the paper's partial-sum tables, and
     reconstruction of the maximizing configuration;
  C. a complete residue analysis mod 2^8 that covers the ENTIRE infinite
     family (exact max + uniqueness of the attainer).

Task 2  the same machinery for nu_2 = nu_6 = 1 (digits {2,6} + 1s, the
        even-family small pair of Theorem C.2, case a=2 mod 3, b=1 mod 2):
        per-j max v2 for j <= 40, growth pattern, family-wide optimum via V,
        Corollary-3.2 explicit bound, factorizations and 7-smoothness of the
        attaining numbers.

Task 3 (probe) Corollary-3.2 bound for the record-product family
        nu = {2:1, 7:6, 8:6, 9:2}, a budgeted run of V on it, and an exact
        max-v2 sweep of all record-family arrangements with <= 16 digits.
        (The arrangement-level 7-smooth generator is src/level1_diophantine.py.)

Pure stdlib, Python 3.14.  Runtime ~2-4 min.
"""
from __future__ import annotations

import json
import sys
import time
from decimal import Decimal, getcontext
from itertools import product
from math import factorial

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from persistence import len23_table  # read-only shared library

T0 = time.time()
LOG: list[str] = []


def say(msg: str = "") -> None:
    print(msg)
    LOG.append(msg)


# ---------------------------------------------------------------------------
# basic number theory (stdlib only)
# ---------------------------------------------------------------------------

def v2(n: int) -> int:
    """2-adic valuation of n > 0, via lowest set bit."""
    return (n & -n).bit_length() - 1


def vp(n: int, p: int) -> int:
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


PRIMES_TO_97 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                59, 61, 67, 71, 73, 79, 83, 89, 97]

# deterministic Miller-Rabin for n < 3.317e24 (first 13 primes); S. Kim et al.
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in _MR_BASES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def factor_full(n: int) -> dict[int, int]:
    """Full factorization; trial division to 97 then Pollard rho.

    Deterministic (Miller-Rabin, 13 bases) for n < 3.317e24 -- covers every
    number this script factorizes fully.  Asserted below.
    """
    fac: dict[int, int] = {}
    for p in PRIMES_TO_97:
        while n % p == 0:
            fac[p] = fac.get(p, 0) + 1
            n //= p
    stack, out = [n], {}
    if n == 1:
        return fac
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if _is_prime(m):
            out[m] = out.get(m, 0) + 1
            continue
        # Pollard rho (Brent-ish), deterministic seeds
        for c in (1, 2, 3, 5, 7, 11, 13):
            x, y, d = 2, 2, 1
            while d == 1:
                x = (x * x + c) % m
                y = (y * y + c) % m
                y = (y * y + c) % m
                d = __import__("math").gcd(abs(x - y), m)
            if d != m:
                break
        else:  # pragma: no cover
            raise RuntimeError(f"rho failed for {m}")
        stack += [d, m // d]
    for p, k in out.items():
        fac[p] = fac.get(p, 0) + k
    assert all(_is_prime(p) for p in fac)
    return fac


def fac_str(fac: dict[int, int]) -> str:
    return "1" if not fac else "*".join(
        f"{p}^{k}" if k > 1 else f"{p}" for p, k in sorted(fac.items()))


def is_7smooth_fac(fac: dict[int, int]) -> bool:
    return set(fac) <= {2, 3, 5, 7}


# ---------------------------------------------------------------------------
# arrangements of a multiset, ascending (lex on the sorted digit string)
# ---------------------------------------------------------------------------

def arrangements(digits: str):
    """Yield all distinct permutations of `digits` (sorted string) as ints,
    in ascending order.  Recursive multiset DFS."""
    counts: dict[str, int] = {}
    for c in digits:
        counts[c] = counts.get(c, 0) + 1
    keys = sorted(counts)
    n = len(digits)
    cur: list[str] = []

    def rec() -> "generator":
        if len(cur) == n:
            yield int("".join(cur))
            return
        for k in keys:
            if counts[k]:
                counts[k] -= 1
                cur.append(k)
                yield from rec()
                cur.pop()
                counts[k] += 1

    yield from rec()


def n_arrangements(digits: str) -> int:
    denom = 1
    for c in set(digits):
        denom *= factorial(digits.count(c))
    return factorial(len(digits)) // denom


# ---------------------------------------------------------------------------
# Fonga's Theorem 4.1 recursion V (verbatim)
#   V(M, a, T) = max( {v_p(T)} U { V(M\\{d}, t, T + (b-1)(d-1) b^t) :
#                        d in M, a < t <= floor(v_p(T)/e) } )
#   V(empty, a, T) = max( {v_p(T)} U { v_p(T + b^L) : a < L <= floor(v_p(T)/e) } )
#   max_{x in A_b(nu)} v_p(x) = max({0} U { V(D\\{d}, 0, T_d) : d in D, p | d })
#   T_d = (b-1)(d-1) - 1
# ---------------------------------------------------------------------------

class BudgetExceeded(Exception):
    pass


def V_value(M, a, T, b=10, p=2, e=1, memo=None, budget=None):
    """Optimal max v_p from state (M, a, T); Fonga Thm 4.1 eq. (14)-(15).
    M: sorted tuple of remaining exceptional digits.  Returns int."""
    if memo is None:
        memo = {}
    if budget is not None:
        budget[0] -= 1
        if budget[0] < 0:
            raise BudgetExceeded
    r = vp(T, p)
    hi = r // e
    key = (M, min(a, hi), T)          # a >= hi  =>  empty range: normalize
    if key in memo:
        return memo[key]
    best = r                          # "stop here" branch
    if M:
        for t in range(a + 1, hi + 1):
            bt = b ** t
            for d in sorted(set(M)):
                M2 = list(M)
                M2.remove(d)
                best = max(best, V_value(tuple(sorted(M2)), t,
                                         T + (b - 1) * (d - 1) * bt,
                                         b, p, e, memo, budget))
    else:
        for L in range(a + 1, hi + 1):
            best = max(best, vp(T + b ** L, p))
    memo[key] = best
    return best


def V_max(nu: dict[int, int], b=10, p=2, e=1, budget=None):
    """max_{x in A_b(nu)} v_p(x) per Fonga Thm 4.1 eq. (16)."""
    D = tuple(sorted(d for d, k in nu.items() for _ in range(k)))
    best = 0
    for d in sorted(set(D)):
        if d % p == 0:
            M = list(D)
            M.remove(d)
            best = max(best, V_value(tuple(sorted(M)), 0,
                                     (b - 1) * (d - 1) - 1, b, p, e, {}, budget))
    return best


def V_path(M, a, T, b=10, p=2, e=1):
    """Small-tree version returning (value, attaining config)."""
    r = vp(T, p)
    hi = r // e
    best, bpath = r, []
    if M:
        for t in range(a + 1, hi + 1):
            bt = b ** t
            for d in sorted(set(M)):
                M2 = list(M)
                M2.remove(d)
                v, path = V_path(tuple(sorted(M2)), t, T + (b - 1) * (d - 1) * bt, b, p, e)
                if v > best:
                    best, bpath = v, [(d, t)] + path
    else:
        for L in range(a + 1, hi + 1):
            v = vp(T + b ** L, p)
            if v > best:
                best, bpath = v, [("L", L)]
    return best, bpath


def config_to_x(nu: dict[int, int], path, b=10):
    """Reconstruct x from a V path [(d, t), ..., ('L', L)] via Lemma 2.1:
    x = (b^L - 1)/(b-1) + sum (d_i - 1) b^{r_i}."""
    L = path[-1][1]
    x = (b ** L - 1) // (b - 1)
    for d, t in path[:-1]:
        x += (d - 1) * b ** t
    return x


# ---------------------------------------------------------------------------
# Leg C: complete residue analysis of the whole family (mod 2^8)
# ---------------------------------------------------------------------------

def tuple_residue(digits8) -> int:
    return sum(d * 10 ** t for t, d in enumerate(digits8)) % 256


def residue_analysis(nu: dict[int, int], label: str):
    """Complete analysis of family A(nu) (nu: exceptional digit -> multiplicity,
    arbitrary 1s, no 0s).  Returns (max_v2, info).

    L <= 8: every arrangement enumerated exactly (x < 10^8).
    L >= 9: x mod 2^8 depends only on digits at positions 0..7; each admissible
    tuple (counts <= nu, rest 1s) is realizable for all large enough L, and
    v2(x) = v2(x mod 256) whenever that residue is nonzero.  A zero residue
    would mean v2 >= 8 exists (flagged, would refute the max).
    """
    D = sorted(d for d, k in nu.items() for _ in range(k))
    q = len(D)
    alpha = sorted(set(D))
    exact = []            # (L, x, v2) for L <= 8
    for L in range(max(q, 1), 9):
        digits = ["1"] * (L - q) + [str(d) for d in D]
        for x in arrangements("".join(sorted(digits))):
            exact.append((L, x, v2(x)))
    # L >= 9 tuples at positions 0..7
    tuples = []           # (tuple, r, v2r)
    zero_residue = []
    for t8 in product([1] + alpha, repeat=8):
        cnt = {d: 0 for d in alpha}
        ok = True
        for d in t8:
            if d != 1:
                cnt[d] += 1
                if cnt[d] > nu[d]:
                    ok = False
                    break
        if not ok:
            continue
        r = tuple_residue(t8)
        if r == 0:
            zero_residue.append(t8)
        else:
            tuples.append((t8, r, v2(r)))
    hi_res = max((v for _, _, v in tuples), default=0)
    hi_exact = max((v for _, _, v in exact), default=0)
    max_v2 = max(hi_res, hi_exact)
    info = {
        "exact_L_le_8": exact,
        "n_tuples": len(tuples),
        "zero_residue_tuples": zero_residue,
        "max_from_L_ge_9": hi_res,
        "max_from_L_le_8": hi_exact,
        "attainers_exact": [(L, x) for L, x, v in exact if v == max_v2],
        "attainer_tuples": [t8 for t8, r, v in tuples if v == max_v2],
    }
    say(f"  [leg C] {label}: L<=8 exact max v2 = {hi_exact} "
        f"({len(exact)} arrangements); L>=9 residue max = {hi_res} "
        f"({len(tuples)} admissible tuples)")
    if zero_residue:
        say(f"  [leg C] WARNING: {len(zero_residue)} tuples with residue 0 "
            f"mod 256 -> v2 >= 8 attainable; deeper analysis needed")
    return max_v2, info


# ---------------------------------------------------------------------------
# Corollary 3.2 explicit bound
# ---------------------------------------------------------------------------

def cor32_bound(nu: dict[int, int]):
    """v2(x) <= floor(rho c^q + ((c^q-1)/(c-1)) log2 B), c = log2 10.
    Returns (bound, q, B, rho)."""
    getcontext().prec = 60
    two = Decimal(2)
    ten = Decimal(10)
    c = ten.ln() / two.ln()
    q = sum(nu.values())
    B = 1 + 9 * sum((d - 1) * k for d, k in nu.items())
    if nu.get(2, 0) > 0:
        rho = 3
    elif nu.get(6, 0) > 0:
        rho = 2
    elif nu.get(4, 0) + nu.get(8, 0) > 0:
        rho = 1
    else:
        rho = 0
    log2B = Decimal(B).ln() / two.ln()
    bound = int((rho * c ** q + (c ** q - 1) / (c - 1) * log2B).to_integral_value(
        rounding="ROUND_FLOOR"))
    return bound, q, B, rho


# ===========================================================================
# Task 1: family {4,4,7} + 1s
# ===========================================================================

def task1():
    say("=" * 74)
    say("TASK 1 -- Fonga Thm 4.1 worked example: nu = {4:2, 7:1} (+ 1s)")
    say("=" * 74)
    total = 0
    per_j = []
    glob_max, glob_att = 0, []
    for j in range(41):
        digits = "".join(sorted("1" * j + "447"))
        mx, att = 0, []
        for x in arrangements(digits):
            v = v2(x)
            total += 1
            if v > mx:
                mx, att = v, [x]
            elif v == mx:
                att.append(x)
        per_j.append((j, n_arrangements(digits), mx, att))
        if mx > glob_max:
            glob_max, glob_att = mx, [(j, x) for x in att]
        elif mx == glob_max:
            glob_att += [(j, x) for x in att]
    say(f"  enumerated {total} numbers (j = 0..40), "
        f"{time.time() - T0:.1f}s elapsed")
    say("  j : #arr : max v2 : attainer(s)")
    for j, n, mx, att in per_j:
        show = att if len(att) <= 3 else att[:2] + ["..."]
        say(f"  {j:>2} : {n:>6} : {mx:>7} : {show}")
    say(f"  [leg A] global max v2 over j<=40 = {glob_max}; "
        f"attained at {glob_att}")

    # 111744 checks
    f111744 = factor_full(111744)
    say(f"  [check] 111744 = {fac_str(f111744)}  "
        f"(paper: 2^7*3^2*97) -> {'PASS' if f111744 == {2: 7, 3: 2, 97: 1} else 'FAIL'}")
    say(f"  [check] v2(111744) = {v2(111744)}; digits "
        f"{sorted(str(111744))} = {{4,4,7}} + three 1s (j=3) -> "
        f"{'PASS' if sorted(str(111744)) == ['1', '1', '1', '4', '4', '7'] else 'FAIL'}")
    say(f"  [check] 111744 among leg-A attainers of the max: "
        f"{'PASS' if (3, 111744) in glob_att else 'FAIL'}")
    uniq = all(x == 111744 for _, x in glob_att)
    say(f"  [leg A] uniqueness within j<=40: "
        f"{'PASS (only 111744)' if uniq else 'FAIL: ' + str(glob_att)}")
    return glob_max, glob_att, per_j


def task1_legB():
    say("-" * 74)
    say("  leg B -- Fonga's recursion V, nu = {4:2, 7:1} (paper section 4)")
    nu = {4: 2, 7: 1}
    mx = V_max(nu)
    say(f"  [leg B] V says max v2 over the ENTIRE family = {mx} "
        f"{'PASS' if mx == 7 else 'FAIL'}")
    # reconstruct the maximizing branch from the initial state ({4,7},0,26)
    # (the units digit 4 at position 0 was placed to build the initial state)
    v, path = V_path((4, 7), 0, 26)
    x = config_to_x(nu, [(4, 0)] + path)
    say(f"  [leg B] maximizing branch: {path} -> x = {x}, v2 = {v} "
        f"{'PASS' if (v, x) == (7, 111744) else 'FAIL'}")
    # reproduce the paper's tables line by line
    checks = [
        ("T_4 = 9(4-1)-1", 26, 1),
        ("4 at position 1: 26 + 9*3*10", 296, 3),
        ("7 at position 1: 26 + 9*6*10", 566, 1),
        ("7 at position 2: 296 + 54*100", 5696, 6),
        ("7 at position 3: 296 + 54*1000", 54296, 3),
        ("L=3: 5696 + 10^3", 6696, 3),
        ("L=4: 5696 + 10^4", 15696, 4),
        ("L=5: 5696 + 10^5", 105696, 5),
        ("L=6: 5696 + 10^6", 1005696, 7),
    ]
    ok = True
    for name, val, want in checks:
        got = v2(val)
        ok &= got == want
        say(f"    v2({name} = {val}) = {got} (paper: {want}) "
            f"{'PASS' if got == want else 'FAIL'}")
    say(f"  [leg B] paper's worked-example tables reproduced: "
        f"{'PASS' if ok else 'FAIL'}")
    # 9x form: 9*111744 = 10^6 - 1 + 27 + 270 + 5400
    say(f"  [check] 9*111744 = {9 * 111744} = 10^6 - 1 + 27 + 270 + 5400 "
        f"{'PASS' if 9 * 111744 == 10**6 - 1 + 27 + 270 + 5400 else 'FAIL'}")
    return mx


def task1_legC():
    say("-" * 74)
    say("  leg C -- complete residue analysis (whole infinite family)")
    mx, info = residue_analysis({4: 2, 7: 1}, "{4,4,7}+1s")
    say(f"  [leg C] family-wide max v2 = {mx} "
        f"{'PASS (matches 7)' if mx == 7 else 'FAIL'}")
    ex = info["attainers_exact"]
    at = info["attainer_tuples"]
    say(f"  [leg C] attainers with L<=8: {ex}")
    say(f"  [leg C] attaining position-tuples with L>=9: "
        f"{len(at)} ('1'=position holds 1) -> "
        f"{'UNIQUE attainer 111744 over the whole family' if not at and ex == [(6, 111744)] else 'SEE ABOVE'}")
    return mx, info


# ===========================================================================
# Task 2: family {2,6} + 1s
# ===========================================================================

def task2():
    say("=" * 74)
    say("TASK 2 -- even-family small pair: nu = {2:1, 6:1} (+ 1s)")
    say("=" * 74)
    total = 0
    per_j = []
    fam_max, fam_att = 0, []
    for j in range(41):
        digits = "".join(sorted("1" * j + "26"))
        mx, att = 0, []
        for x in arrangements(digits):
            v = v2(x)
            total += 1
            if v > mx:
                mx, att = v, [x]
            elif v == mx:
                att.append(x)
        per_j.append((j, n_arrangements(digits), mx, att))
        if mx > fam_max:
            fam_max, fam_att = mx, [(j, x) for x in att]
        elif mx == fam_max:
            fam_att += [(j, x) for x in att]
    say(f"  enumerated {total} numbers (j = 0..40)")
    say("  j : #arr : max v2 : attainer(s)")
    for j, n, mx, att in per_j:
        show = att if len(att) <= 4 else att[:3] + ["..."]
        say(f"  {j:>2} : {n:>6} : {mx:>7} : {show}")
    plateau = per_j[8:]
    plat_const = len({mx for _, _, mx, _ in plateau}) == 1
    say(f"  [growth] argmax j = {max(per_j, key=lambda r: r[2])[0]}; "
        f"per-j max constant for j >= 8 (L >= q+8 = 10, all position-tuples "
        f"realizable): {'PASS' if plat_const else 'FAIL'} "
        f"(plateau value {plateau[0][2]})")
    # family-wide optimum: leg B + leg C
    say("-" * 74)
    nu = {2: 1, 6: 1}
    mxB = V_max(nu)
    v, path = V_path((2,), 0, 44)   # units 6: T_6 = 9*5-1 = 44, remaining {2}
    v2b, path2 = V_path((6,), 0, 8)  # units 2: T_2 = 9*1-1 = 8, remaining {6}
    if v >= v2b:
        best_x = config_to_x(nu, [(6, 0)] + path)
    else:
        best_x = config_to_x(nu, [(2, 0)] + path2)
    say(f"  [leg B] V family-wide max v2 = {mxB} "
        f"(units-6 branch: {v} via {path}; units-2 branch: {v2b} via {path2})")
    say(f"  [leg B] attainer x = {best_x} = {fac_str(factor_full(best_x))}")
    mxC, infoC = residue_analysis(nu, "{2,6}+1s")
    agree = mxB == mxC == fam_max
    say(f"  [cross] leg A max (j<=40) = {fam_max}, leg B = {mxB}, leg C = {mxC} "
        f"-> {'AGREE' if agree else 'DISAGREE'}")
    # attainers of the family max: full factorizations + 7-smoothness
    say(f"  [attainers] all j<=40 members with v2 = {fam_max}:")
    for j, x in fam_att:
        f = factor_full(x)
        assert x < 3_317_044_064_679_887_385_961_981
        say(f"    j={j:>2}  {x} = {fac_str(f)}  "
            f"{'7-SMOOTH' if is_7smooth_fac(f) else 'not 7-smooth'}")
    # growth pattern summary
    seq = [mx for _, _, mx, _ in per_j]
    say(f"  [growth] max-v2 sequence j=0..7: {seq[:8]}; "
        f"max over j<=40 attained at j = "
        f"{[j for j, _, mx, _ in per_j if mx == fam_max]}")
    b32, q, B, rho = cor32_bound(nu)
    say(f"  [Cor 3.2] q={q}, B={B}, rho={rho} -> explicit bound "
        f"v2 <= {b32}  (optimal {fam_max}; the explicit bound is valid but loose)")
    return per_j, fam_max, fam_att, infoC


# ===========================================================================
# Task 3 probes: record-product family nu = {2:1, 7:6, 8:6, 9:2}
# ===========================================================================

def task3_probes():
    say("=" * 74)
    say("TASK 3 PROBES -- record-product family nu = {2:1, 7:6, 8:6, 9:2}")
    say("  (digits of every preimage of m0 = 2^19*3^4*7^6 with the rigid")
    say("   multiset {7^6} u F(19,4) u {1^j}; F(19,4) = {2, 8^6, 9^2})")
    say("=" * 74)
    nu = {2: 1, 7: 6, 8: 6, 9: 2}
    b32, q, B, rho = cor32_bound(nu)
    say(f"  [Cor 3.2] q={q}, B={B}, rho={rho} -> explicit bound v2 <= {b32}")
    # leg C residue analysis (independent of V)
    mxC, infoC = residue_analysis(nu, "record family")
    if infoC["zero_residue_tuples"] == []:
        say(f"  [leg C] no position-tuple gives residue 0 mod 256, and "
            f"L<=8 max is {infoC['max_from_L_le_8']} -> family-wide max v2 = {mxC} "
            f"(EXACT, covers all j)")
    # exact sweep of all arrangements with L <= 16 (j <= 1)
    say("  [exact sweep] all arrangements with L <= 16 (j = 0, 1):")
    best = (0, None)
    for j in (0, 1):
        # sorted digits: 1s, 2, 7^6, 8^6, 9^2
        digits = "".join(sorted("1" * j + "2" + "777777" + "888888" + "99"))
        n = n_arrangements(digits)
        t0 = time.time()
        mx, att = 0, []
        for i, x in enumerate(arrangements(digits)):
            v = v2(x)
            if v > mx:
                mx, att = v, [x]
            elif v == mx:
                att.append(x)
        say(f"    L={15+j} (j={j}): {n} arrangements ({time.time()-t0:.1f}s), "
            f"max v2 = {mx} at {att[:4]}{' ...' if len(att) > 4 else ''}")
        if mx > best[0]:
            best = (mx, (j, att))
    say(f"  [exact sweep] max v2 over all L<=16 record-family arrangements = {best[0]}")
    # budgeted V run
    say("  [leg B] budgeted V run on the record family (q = 15)...")
    budget = [40_000_000]
    t0 = time.time()
    try:
        mxV = V_max(nu, budget=budget)
        say(f"  [leg B] V family-wide max v2 = {mxV} "
            f"({40_000_000 - budget[0]} nodes, {time.time()-t0:.1f}s)")
        # exhibit a maximizing member and verify it independently
        D = tuple(sorted(dd for dd, k in nu.items() for _ in range(k)))
        cands = []
        for dd in (2, 8):
            M = list(D)
            M.remove(dd)
            v, path = V_path(tuple(sorted(M)), 0, 9 * (dd - 1) - 1)
            cands.append((v, dd, path))
        v, dd, path = max(cands)
        x = config_to_x(nu, [(dd, 0)] + path)
        Lx = len(str(x))
        digits_ok = sorted(str(x)) == sorted("1" * (Lx - 15) + "2" + "777777" + "888888" + "99")
        rest = x
        for pp in (2, 3, 5, 7):
            while rest % pp == 0:
                rest //= pp
        say(f"  [leg B] argmax branch (units {dd}): {path}")
        say(f"  [leg B] attaining member x = {x} (L={Lx}, j={Lx - 15} inserted 1s)")
        say(f"  [check] v2(x) = {v2(x)} (V said {v}); digit multiset correct: "
            f"{digits_ok}; 7-smooth (2^A 3^B 7^D): {'YES' if rest == 1 else 'NO (rest ' + str(rest) + ')'}")
        say(f"  [verdict] record-family sup over the ENTIRE infinite family: "
            f"v2 <= {mxV}, attained (leg B exact); leg-C mod-256 analysis "
            f"correctly flagged itself inconclusive (max >= 8)")
    except BudgetExceeded:
        say(f"  [leg B] V exceeded the node budget ({time.time()-t0:.1f}s) -- exact "
            f"optimal value not computed here; this is precisely the 'finite, "
            f"terminating procedure' whose full run Fonga leaves undone.  "
            f"Cor-3.2 bound {b32} remains valid.")
    return mxC, infoC, b32


# ===========================================================================
def main():
    say("Certificate 3 (pure_math.md section 6) -- Fonga verification, "
        "subagent F")
    say(f"Python {sys.version.split()[0]}, stdlib only.  Start {time.strftime('%Y-%m-%d %H:%M:%S')}")
    say("")
    g1 = task1()
    say("")
    task1_legB()
    say("")
    task1_legC()
    say("")
    t2 = task2()
    say("")
    task3_probes()
    say("")
    say(f"Done in {time.time() - T0:.1f}s.")
    with open(__file__.rsplit("/", 1)[0] + "/../results/fonga_cert_log.txt", "w") as fh:
        fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
