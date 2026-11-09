"""Independent semantic validation of lib_sT against PROVED results of
arXiv:2008.01164v2 (Berlow). All checks must pass before any conjecture work.

V1  Theorem 2.3: pi avoids T^r  =>  s_T(pi) = pi^r.  Tested for all pi in S_5
    and several T (incl. a 3-element set and the target pairs).
V2  Theorem 1.5: T = {231, 321} is reduced and hat-closed => s_T is a bijection
    and r . s_T . r = s_T^{-1}. Tested on S_6.
V3  Lemma 4.3: explicit action of s_{123,132} on half-decreasing permutations
    (decreasing half fixed; remaining positions shift left cyclically).
V4  Theorem 4.5: periodic points of s_{123,132} = half-decreasing perms (S_3..S_6).
V5  Corollary 4.9: periodic points of s_{312,321} = half-increasing perms (S_3..S_6).
V6  (s_T(pi))_n = pi_1 for T with min pattern length 3 (both target pairs, S_3..S_7).
V7  id <-> reverse under both target maps, n = 1..6 (tiny boundaries included).
"""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib_sT import (s_T, reverse_word, complement, avoids, rev_set,
                    periodic_points, half_decreasing)

res = {}
ok_all = True


def check(name, cond):
    global ok_all
    res[name] = bool(cond)
    ok_all = ok_all and bool(cond)
    print(("PASS " if cond else "FAIL ") + name, flush=True)


Tsets = {
    "123_132": ((1, 2, 3), (1, 3, 2)),
    "132_213": ((1, 3, 2), (2, 1, 3)),
    "231_213": ((2, 3, 1), (2, 1, 3)),
    "triple": ((1, 2, 3), (2, 1, 3), (3, 1, 2)),
}

# V1: Theorem 2.3
for name, T in Tsets.items():
    Tr = rev_set(T)
    bad = [pi for pi in itertools.permutations(range(1, 6))
           if avoids(pi, Tr) and s_T(pi, T) != reverse_word(pi)]
    check(f"V1_thm2.3_{name}", not bad)

# V2: Theorem 1.5 for T={231,321} on S_6
T = ((2, 3, 1), (3, 2, 1))
S6 = list(itertools.permutations(range(1, 7)))
imgs = {s_T(p, T) for p in S6}
check("V2_thm1.5_bijective_231_321", len(imgs) == len(S6))
check("V2_thm1.5_inverse_rsr",
      all(reverse_word(s_T(reverse_word(s_T(p, T)), T)) == p for p in S6))

# V3: Lemma 4.3 explicit action
def lemma43_expect(pi):
    n = len(pi)
    if n % 2 == 1:
        dec = [i for i in range(1, n + 1) if i % 2 == 0]            # 2,4,..,n-1
    else:
        dec = [i for i in range(3, n + 1, 2)] if n >= 4 else []     # 3,5,..,n-1
    others = [i for i in range(1, n + 1) if i not in dec]
    vals = [pi[i - 1] for i in others]
    shifted = vals[1:] + vals[:1]
    out = [None] * n
    for pos, v in zip(others, shifted):
        out[pos - 1] = v
    for i in dec:
        out[i - 1] = pi[i - 1]
    return tuple(out)

T132 = Tsets["123_132"]
bad = []
for n in (3, 4, 5, 6, 7):
    for pi in itertools.permutations(range(1, n + 1)):
        if half_decreasing(pi) and s_T(pi, T132) != lemma43_expect(pi):
            bad.append((n, pi, s_T(pi, T132), lemma43_expect(pi)))
check("V3_lemma4.3_action", not bad)

# V4/V5: periodic point classifications
for label, T, pred in [
    ("123_132", Tsets["123_132"], half_decreasing),
    ("312_321", ((3, 1, 2), (3, 2, 1)), lambda p: half_decreasing(complement(p))),
]:
    for n in (3, 4, 5, 6):
        pp, _, _ = periodic_points(n, T)
        expect = {p for p in itertools.permutations(range(1, n + 1)) if pred(p)}
        check(f"V45_periodic_{label}_n{n}", pp == expect)

# V6: last element property for target maps
bad = []
for name in ("132_213", "231_213"):
    T = Tsets[name]
    for n in range(3, 8):
        for pi in itertools.permutations(range(1, n + 1)):
            if s_T(pi, T)[-1] != pi[0]:
                bad.append((name, n, pi))
check("V6_last_elem_pi1", not bad)

# V7: id <-> reverse for target maps, n = 1..6
bad = []
for name in ("132_213", "231_213"):
    T = Tsets[name]
    for n in range(1, 7):
        ident = tuple(range(1, n + 1))
        rev = reverse_word(ident)
        if not (s_T(ident, T) == rev and s_T(rev, T) == ident):
            bad.append((name, n))
check("V7_id_rev_2cycle", not bad)

print(json.dumps({"all_ok": ok_all, "checks": res}, indent=1))
with open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                       "work", "semantic-validation.json"), "w") as f:
    json.dump({"all_ok": ok_all, "checks": res}, f, indent=1)
sys.exit(0 if ok_all else 1)
