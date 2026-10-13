"""Exact arithmetic checks of the geometric constants; not a proof certificate."""
from fractions import Fraction as F
from itertools import product
import json

points = [tuple(F(x, 6) for x in r) for r in product(range(7), repeat=4)
          if sum(r) == 6]
checks = 0
for r in points:
    for s in points:
        length2 = 2 * sum((a-b)**2 for a, b in zip(r, s))
        midpoint2 = 2 * sum(((a+b)/2)**2 for a, b in zip(r, s)) - F(1, 2)
        dot = 2 * sum(a*b for a, b in zip(r, s)) - F(1, 2)
        assert midpoint2 - length2/4 == dot
        assert dot >= -F(1, 2) and midpoint2 >= 0 and length2 <= 4
        checks += 1
# Squared mass and line maximum avoid approximating radicals.
mass2 = F(16, 15)**2 * 2
maximum2 = F(16, 25)**2 * 15
assert mass2 / maximum2 == F(30, 81)
assert mass2 / maximum2 / 2 == F(15, 81)
assert 2 * (F(19, 10) + F(1, 2)) == F(24, 5)
for i in range(31):
    z = F(1, 2) + F(i, 60)
    r, s = (z, 1-z, 0, 0), (0, 0, z, 1-z)
    length2 = 2 * sum((a-b)**2 for a, b in zip(r, s))
    assert length2 == 2 + 8*(z-F(1, 2))**2
    assert sum(a*b for a, b in zip(r, s)) == 0
print(json.dumps({"passed": True, "exact_barycentric_chord_pairs": checks,
                  "opposite_edge_checks": 31,
                  "scope": "Finite exact arithmetic checks; the general proof is in main.tex."}, indent=2))
