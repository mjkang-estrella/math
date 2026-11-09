"""Gate B check 3: hook Lemma 1, Lemma 2 weight formula, the c = 5 pair, and small source claims.

Usage: python3 -I hooks.py <scripts dir>
"""
import itertools
import json
import math
import random
import sys
from collections import Counter

sys.path.insert(0, sys.argv[1])
from jdt import delete, minors_multiset, all_syt, hook  # noqa: E402


def H(w):
    """Hook of the word w in {A, L}^N: letter t says where entry t + 2 goes (arm or leg)."""
    n = len(w) + 1
    arm = [1] + [t + 2 for t, c in enumerate(w) if c == "A"]
    return hook(arm, n)


def formula(w, k):
    N = len(w)
    c = Counter()
    for P in itertools.combinations(range(1, N + 1), N - k):
        c[H("".join(w[p - 1] for p in P))] += math.factorial(k) * P[0]
    return c


out = {}
# Lemma 1 on all words with N <= 9.
ok1 = True
for N in range(1, 10):
    for w in itertools.product("AL", repeat=N):
        w = "".join(w)
        T = H(w)
        for m in range(1, N + 2):
            q = 1 if m <= 2 else m - 1
            if delete(T, m) != H(w[:q - 1] + w[q:]):
                ok1 = False
out["lemma1_all_words_N_le_9"] = ok1

# Lemma 2: exhaustive for N <= 8 and all 1 <= k <= N - 1, plus random larger cases.
ok2, cases = True, 0
for N in range(2, 9):
    for w in itertools.product("AL", repeat=N):
        w = "".join(w)
        for k in range(1, N):
            cases += 1
            if minors_multiset(H(w), k) != formula(w, k):
                ok2 = False
rng = random.Random(20261102)
for _ in range(40):
    N = rng.randint(9, 13)
    w = "".join(rng.choice("AL") for _ in range(N))
    k = rng.randint(1, N - 1)
    cases += 1
    if minors_multiset(H(w), k) != formula(w, k):
        ok2 = False
out["lemma2_cases"] = cases
out["lemma2_ok"] = ok2

# c = 5 pair: k = 11, n = 16.
U1 = hook([1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 16], 16)
U2 = hook([1, 4, 5, 6, 7, 8, 12, 13, 14, 15], 16)
out["c5_legs"] = [[r[0] for r in U1[1:]], [r[0] for r in U2[1:]]]
out["c5_distinct"] = U1 != U2
out["c5_equal_mM11"] = minors_multiset(U1, 11) == minors_multiset(U2, 11)
out["c5_total"] = sum(minors_multiset(U1, 11).values())

# Smallest hook collision for c = 4 and c = 5 via the formula (exhaustive over words).
def first_hook_collision(c, Nmax):
    for N in range(c, Nmax + 1):
        k = N + 1 - c
        seen = {}
        for w in itertools.product("AL", repeat=N):
            w = "".join(w)
            key = tuple(sorted(formula(w, k).items()))
            if key in seen:
                return {"n": N + 1, "k": k, "pair": [seen[key], w]}
            seen[key] = w
    return None
out["first_hook_collision_c4"] = first_hook_collision(4, 13)

# Source claims: mM_2 injective at n = 6, 7, not at n = 5; M_1 sets injective n >= 5 (n = 5..8);
# M_2 sets injective exactly from n = 8 (check n = 7 fails, n = 8, 9 injective).
def inj(n, k, sets):
    keys = Counter()
    for T in all_syt(n):
        mm = minors_multiset(T, k)
        keys[frozenset(mm) if sets else frozenset(mm.items())] += 1
    return all(v == 1 for v in keys.values())
out["source_mM2_injective"] = {n: inj(n, 2, False) for n in (5, 6, 7)}
out["source_M1_sets_injective"] = {n: inj(n, 1, True) for n in (4, 5, 6, 7, 8)}
out["source_M2_sets_injective"] = {n: inj(n, 2, True) for n in (7, 8, 9)}
print(json.dumps(out))
