"""Independent direct replay of primary Definition 1, for review only."""
import json
from pathlib import Path
X, Y = [0], [0]
used, blocked = set(), set()
for n in range(1, 57):
    x = 1
    while x in used:
        x += 1
    y = x + 1
    while y in used or y - x in blocked:
        y += 1
    X.append(x)
    Y.append(y)
    used.update([x, y])
    blocked.update([y - x, y + x])
expected_x = [0, 1, 3, 4, 6, 7, 9, 10, 12, 14, 15, 17, 18, 20, 21, 23]
expected_y = [0, 2, 5, 8, 11, 13, 16, 19, 22, 25, 28, 31, 33, 36, 39, 42]
assert X[:16] == expected_x
assert Y[:16] == expected_y
values = {'X20': X[20], 'Y20': Y[20], 'X56': X[56], 'Y30': Y[30],
          'lhs': X[Y[20]] + Y[X[20]], 'rhs': 2*X[20] + 2*Y[20] - 1}
assert values == {'X20': 30, 'Y20': 56, 'X56': 86, 'Y30': 84, 'lhs': 170, 'rhs': 171}
print(json.dumps(values, indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(values, indent=2)+'\n')
