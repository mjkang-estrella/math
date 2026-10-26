"""Independent permutation enumeration for the ideal-DP polynomial."""
from itertools import combinations, permutations
from collections import Counter
import json
import numpy as np
from pathlib import Path
from screen import polynomial

rng = np.random.default_rng(904472)
records = []
for n in range(5, 9):
    for trial in range(5):
        chain = sorted(map(int, rng.choice(n, size=3, replace=False)))
        edges = {(a, b) for a, b in combinations(range(n), 2) if rng.random() < .2}
        edges.update(zip(chain, chain[1:]))
        expected = Counter()
        for order in permutations(range(n)):
            position = [0] * n
            for i, v in enumerate(order):
                position[v] = i
            if any(position[a] > position[b] for a, b in edges):
                continue
            gaps = [position[b] - position[a] - 1 for a, b in zip(chain, chain[1:])]
            outside = n - len(chain) - sum(gaps)
            expected[tuple([outside] + gaps)] += 1
        actual, _ = polynomial(n, chain, edges)
        assert actual == expected
        records.append({"n": n, "trial": trial, "linear_extensions": sum(expected.values()),
                        "monomials": len(expected)})
output = {"status": "PASS: exact full permutation enumeration agrees with ideal dynamic programming",
          "posets": len(records), "records": records,
          "scope": "Validates the search implementation on these cases only; not a proof of Conjecture 4.7."}
Path('counting-check.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({k: v for k, v in output.items() if k != 'records'}))
