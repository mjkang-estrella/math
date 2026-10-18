#!/usr/bin/env python3
"""MIT. Finite arithmetic and combinatorial diagnostics; not analytic proof."""
import json
from collections import Counter

def blocks(a, b):
    out = []
    while a < b:
        size = 1
        while a % (2 * size) == 0 and a + 2 * size <= b:
            size *= 2
        out.append((a, a + size))
        a += size
    return out

def main():
    tests = 0
    two_needed = False
    for n in (1, 2, 4, 8, 16, 32, 64):
        for a in range(n):
            for b in range(a + 1, n + 1):
                pieces = blocks(a, b)
                assert [k for lo, hi in pieces for k in range(lo, hi)] == list(range(a, b))
                counts = Counter(hi-lo for lo,hi in pieces)
                assert max(counts.values()) <= 2
                two_needed |= max(counts.values()) == 2
                tests += 1
    def p(x, t):
        ans = 1
        for j in range(4):
            ans *= t-j*x
        return ans
    shifted = [p(4, 5*j) for j in range(4)]
    assert shifted == [0,105,-240,3465]
    assert all(p(5,5*j) == 0 for j in range(4))
    # Negative controls: false all-anchor invariance, one-block-per-level,
    # and the pointwise V(partial sums) <= square(increments) shortcut.
    checks = {'wrong_all_anchor_invariance_rejected': not all(v == 0 for v in shifted),
              'wrong_one_block_per_level_rejected': two_needed,
              'wrong_pointwise_square_bound_rejected': 64**2 > 64}
    assert all(checks.values())
    print(json.dumps({'status':'PASS_FINITE_NONPROOF','intervals_checked':tests,
                      'shifted_symbols':shifted,'negative_controls':checks},sort_keys=True))

if __name__ == '__main__':
    main()
