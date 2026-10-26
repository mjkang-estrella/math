"""Independent exact partition classification, Python standard library only.

This is a cross-check, not the Lean certificate. It computes the exact third
coefficient; the formal source endpoint only needs the proved lower bound.
"""
from itertools import combinations, combinations_with_replacement
from math import comb
from pathlib import Path
import json

side = 25
partitions = set()
for a, b in combinations(range(1, side + 1), 2):
    allowed = [x for x in range(1, side + 1) if x not in (a, b)]
    extras = [[c] for c in allowed if c == a + b]
    extras += [[c, d] for c, d in combinations_with_replacement(allowed, 2)
               if c + d == a + b]
    for extra in extras:
        parts = tuple(sorted(allowed + extra))
        assert len(parts) <= side and sum(parts) == 325 and len(set(parts)) == 23
        assert parts not in partitions
        partitions.add(parts)
assert len(partitions) == 2444
cut = [comb(25, 5), comb(25, 21) * comb(4, 3), 23 * len(partitions) + 6900]
assert cut == [53130, 50600, 63112]
assert cut[1] < cut[0] and cut[1] < cut[2]
result = {"status": "PASS", "method": "direct missing/repeated-size classification",
          "a25": 1, "a24": 0, "a23": len(partitions), "exact_cut": cut,
          "scope": "Independent arithmetic cross-check; formal endpoint uses third coefficient >=52900"}
Path(__file__).with_name('count-check.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
