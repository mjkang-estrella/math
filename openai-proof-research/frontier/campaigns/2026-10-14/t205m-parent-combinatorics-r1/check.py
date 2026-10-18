#!/usr/bin/env python3
"""MIT. Finite partition diagnostic; not a proof of the all-order lemma."""
import argparse
import json
from pathlib import Path


def partitions(n, cap):
    if n == 0:
        yield ()
        return
    for a in range(min(n, cap), 0, -1):
        for rest in partitions(n - a, a):
            yield (a,) + rest


def predecessors(lam, n):
    lower = lam[4:] + (0,) * min(4, len(lam))
    suffix_lower = [0] * (len(lam) + 1)
    for i in range(len(lam) - 1, -1, -1):
        suffix_lower[i] = suffix_lower[i + 1] + lower[i]

    def rec(i, left, cap, prefix):
        if i == len(lam):
            if left == 0:
                yield tuple(a for a in prefix if a)
            return
        if left < suffix_lower[i]:
            return
        if left > sum(min(cap, a) for a in lam[i:]):
            return
        for a in range(min(lam[i], cap, left), lower[i] - 1, -1):
            yield from rec(i + 1, left - a, a, prefix + (a,))

    yield from rec(0, n, lam[0], ())


def main(top):
    rows = []
    for m in range(7, top + 1):
        n_big = m * (m + 1) // 2
        h = m - 2
        n = h * (h + 1) // 2
        exceptions = {(n,), (1,) * n, (h,) + (1,) * (n - h),
                      (h, 2) + (1,) * (n - h - 2)}
        tested = 0
        bad = []
        for lam in partitions(n_big, m):
            if sum(lam[:4]) < 2 * m + 1:
                continue
            tested += 1
            good = []
            seen = []
            for nu in predecessors(lam, n):
                seen.append(nu)
                if nu not in exceptions:
                    good.append(nu)
                if len(good) == 2:
                    break
            if len(good) < 2:
                bad.append({'lambda': lam, 'predecessors': seen, 'good': good})
        rows.append({'m': m, 'tested': tested, 'bad': bad})
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--top', type=int, default=9)
    args = parser.parse_args()
    result = main(args.top)
    if args.top == 9:
        assert result == json.loads(Path(__file__).with_name('capacity-screen.json').read_text())
    assert all(not row['bad'] for row in result)
    print(json.dumps({'status': 'PASS', 'rows': result,
                      'scope': 'Finite diagnostic only; no independent review or novelty conclusion.'}, indent=2))
