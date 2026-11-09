"""Independent reviewer cross-check: exhaustive DP over all partitions of 325
in the 25x25 box, tracking number of distinct part sizes.

Method differs from scripts/check_counts.py (missing/repeated-size
classification): here every box partition is counted by an explicit
size-by-size dynamic program, so a_r and the three cut coefficients are
computed from first principles with no injection or classification input.
"""
import json
from math import comb
from pathlib import Path

M = N = 25
n = 325
# f[(s, p, d)] = number of multisets over sizes processed so far with
# sum s, p total parts, d distinct sizes present.
f = {(0, 0, 0): 1}
for size in range(1, M + 1):
    g = dict(f)
    for (s, p, d), cnt in f.items():
        # multiplicity m >= 1 for this size (m copies), 0 means skip
        for m in range(1, N - p + 1):
            key = (s + m * size, p + m, d + 1)
            if key[0] <= n:
                g[key] = g.get(key, 0) + cnt
    f = g

assert f[(n, N, 25)] == 1, "staircase unique a25"
counts = {}
for (s, p, d), cnt in f.items():
    if s == n and p <= N:
        counts[d] = counts.get(d, 0) + cnt

a25 = counts.get(25, 0)
a24 = counts.get(24, 0)
a23 = counts.get(23, 0)
assert a25 == 1 and a24 == 0

def coeff(i, j):
    return sum(cnt * comb(r, i) * comb(r - i, j) for r, cnt in counts.items() if r >= i + j)

c205 = coeff(20, 5)
c213 = coeff(21, 3)
c221 = coeff(22, 1)
assert c205 == 53130, c205
assert c213 == 50600, c213
assert c221 >= 52900, c221
cut = [comb(25, 5), comb(25, 21) * comb(4, 3)]
assert cut == [53130, 50600]

result = {
    "status": "PASS",
    "method": "exhaustive size-by-size DP over all 25x25 box partitions of 325",
    "a25": a25, "a24": a24, "a23": a23,
    "cut_20_5": c205, "cut_21_3": c213, "cut_22_1": c221,
    "valley": c213 < c205 and c213 < c221,
}
Path(__file__).with_name("reviewer-dp-check.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
