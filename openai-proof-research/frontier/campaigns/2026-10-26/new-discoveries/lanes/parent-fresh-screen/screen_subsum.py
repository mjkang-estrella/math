#!/usr/bin/env python3
"""Exact finite search of 2605.10512 Conjecture 4; not a universal proof."""
import json
import time
from pathlib import Path


def multiply_binomial(a, step):
    out = a + [0] * step
    for i, v in enumerate(a):
        out[i + step] += v
    return out


def main():
    start = time.monotonic()
    a = [1]
    failures = []
    checks = 0
    for n in range(1, 301):
        step = n
        while True:
            a = multiply_binomial(a, step)
            if step % 2:
                break
            step //= 2
        assert a == a[::-1]
        assert sum(a) == 2 ** (2*n - (2*n).bit_count())
        for k in range(1, len(a) - 1):
            checks += 1
            if a[k] ** 2 < a[k - 1] * a[k + 1]:
                failures.append({'n': n, 'k': k,
                                 'triple': a[k-1:k+2]})
                break
    result = {'source': '2605.10512 Conjecture 4 and Proposition 3.8(a)',
              'recurrence': 'D_n/D_(n-1) = product_(j=0)^v2(n) (1+x^(n/2^j))',
              'arithmetic': 'exact arbitrary-precision Python integers',
              'n_max': 300, 'inequalities_checked': checks, 'failures': failures,
              'unexpected_failure': any(x['n'] not in [3,5,6,7] for x in failures),
              'elapsed_seconds': time.monotonic() - start,
              'qualification': 'Finite screening only; no universal log-concavity proof and no discovery credit.'}
    Path('subsum-screen.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
