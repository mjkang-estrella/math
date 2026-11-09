"""Gate B check 1: the k = 8, n = 12 pair, the source figure, and the Lean certificate lists.

Usage: python3 -I check_pair.py <path to lane TabMinors.lean> <scripts dir>
The Lean file is read as data only (its A1..A8 / B1..B8 literals are parsed with ast.literal_eval).
"""
import ast
import json
import re
import sys
from collections import Counter

sys.path.insert(0, sys.argv[2])
from jdt import delete, is_syt, minors_multiset, hook, transpose, size  # noqa: E402

out = {}
T1 = hook([1, 5, 7, 8, 12], 12)
T2 = hook([1, 2, 3, 7, 10, 11], 12)
out["T1"] = T1
out["T2"] = T2
out["T1_syt"] = is_syt(T1, 12)
out["T2_syt"] = is_syt(T2, 12)
out["T1_ne_T2"] = T1 != T2

# Source figure: T - 8.
Tfig = ((1, 2, 3, 4, 5), (6, 7, 8, 9, 18), (10, 11, 12, 17), (13, 16), (14,), (15,))
Tfig8 = ((1, 2, 3, 4, 5), (6, 7, 8, 16, 17), (9, 10, 11), (12, 15), (13,), (14,))
out["source_figure_T_minus_8"] = delete(Tfig, 8) == Tfig8

# Level-by-level DP, keeping every level so it can be compared with the Lean literals.
def levels(T, k):
    res = []
    level = Counter({T: 1})
    for _ in range(k):
        nxt = Counter()
        for S, w in level.items():
            for m in range(1, size(S) + 1):
                nxt[delete(S, m)] += w
        level = nxt
        res.append(level)
    return res

LA = levels(T1, 8)
LB = levels(T2, 8)
out["total_A8"] = sum(LA[-1].values())
out["total_B8"] = sum(LB[-1].values())
out["mM8_equal"] = LA[-1] == LB[-1]
out["mM8_T1"] = sorted(([list(r) for r in t], c) for t, c in LA[-1].items())
out["distinct_counts_per_level_A"] = [len(L) for L in LA]
out["distinct_counts_per_level_B"] = [len(L) for L in LB]
for k in range(1, 8):
    if minors_multiset(T1, k) == minors_multiset(T2, k):
        out.setdefault("equal_at_smaller_k", []).append(k)

# Transposes and the second pair.
T3 = hook([1, 5, 6, 8, 12], 12)
T4 = hook([1, 2, 3, 6, 10, 11], 12)
out["pair2_equal"] = minors_multiset(T3, 8) == minors_multiset(T4, 8) and T3 != T4
out["transpose_pair1_equal"] = minors_multiset(transpose(T1), 8) == minors_multiset(transpose(T2), 8)

# Compare with the Lean certificate literals (as multisets: Lean lists are merged by `norm`).
src = open(sys.argv[1], encoding="utf-8").read()
cmp = {}
for name, L in [("A", LA), ("B", LB)]:
    for i in range(1, 9):
        m = re.search(r"^def %s%d : List \(Tab × ℕ\) := (.*)$" % (name, i), src, re.M)
        lit = ast.literal_eval(m.group(1))
        names = [tuple(tuple(r) for r in t) for t, _ in lit]
        c = Counter()
        for t, w in lit:
            c[tuple(tuple(r) for r in t)] += w
        cmp["%s%d" % (name, i)] = {
            "matches_independent_dp": c == L[i - 1],
            "no_duplicate_keys": len(names) == len(set(names)),
            "entries": len(lit),
        }
out["lean_literals_vs_independent_dp"] = cmp
print(json.dumps(out, default=list))
