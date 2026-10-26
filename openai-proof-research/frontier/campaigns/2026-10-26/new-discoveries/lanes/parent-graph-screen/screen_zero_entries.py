"""Exploration of literal Conjecture 5, including repeated row/column indices."""
from pathlib import Path
import json
import numpy as np

rng = np.random.default_rng(1932471)
best_ratio = 0.0
best = None
tested = 0
for n in range(3, 12):
    for trial in range(300):
        m = int(rng.integers(3, 12))
        if trial % 2 == 0 and m == n:
            matrix = np.zeros((n, m), dtype=np.int64)
            for _ in range(int(rng.integers(1, n))):
                matrix[np.arange(n), rng.permutation(n)] += 1
        else:
            matrix = rng.integers(1, 5, size=(n, m))
            matrix[rng.random((n, m)) < rng.uniform(.3, .85)] = 0
        zeros = np.argwhere(matrix == 0)
        if len(zeros) < 3:
            continue
        norm = int(matrix.sum(0).max() * matrix.sum(1).max())
        if norm == 0:
            continue
        x, y = zeros.T
        weight = matrix[x[:, None], y[None, :]] * matrix[x[None, :], y[:, None]]
        assert np.array_equal(weight, weight.T) and not np.diag(weight).any()
        limit = min(len(zeros), 35)
        for t in sorted(set([3, 5, 7, limit if limit % 2 else limit-1])):
            if t > len(zeros) or t < 3:
                continue
            for _ in range(3):
                chosen = np.zeros(len(zeros), dtype=bool)
                chosen[rng.choice(len(zeros), size=t, replace=False)] = True
                score = weight[:, chosen].sum(1)
                for _ in range(100):
                    ins, outs = np.flatnonzero(~chosen), np.flatnonzero(chosen)
                    if len(ins) == 0:
                        break
                    gains = score[ins, None] - score[outs][None, :] - weight[np.ix_(ins, outs)]
                    where = np.unravel_index(np.argmax(gains), gains.shape)
                    if gains[where] <= 0:
                        break
                    a, b = int(ins[where[0]]), int(outs[where[1]])
                    chosen[b], chosen[a] = False, True
                    score += weight[:, a] - weight[:, b]
                lhs = int(weight[np.ix_(chosen, chosen)].sum())
                rhs = (t-1) * norm
                tested += 1
                if lhs / rhs > best_ratio:
                    best_ratio = lhs / rhs
                    best = {"matrix": matrix.tolist(), "zeros_selected": zeros[chosen].tolist(),
                            "t": t, "lhs": lhs, "rhs": rhs, "ratio": best_ratio}
                if lhs > rhs:
                    best['status'] = 'EXACT INTEGER HIT: all source/independent/novelty/formal gates pending'
                    Path('zero-entry-hit.json').write_text(json.dumps(best, indent=2) + '\n')
                    print(json.dumps(best), flush=True)
                    raise SystemExit
    print(n, tested, best_ratio, flush=True)
output = {"status": "No violation found; finite heuristic evidence only", "seed": 1932471,
          "subsets_tested": tested, "best": best}
Path('zero-entry-screen.json').write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({k: v for k, v in output.items() if k != 'best'}), flush=True)
