"""W001 diagnostic, not a factoring solver or benchmark.

Preregistered finite claim: every residue-bit stream has GF(2) linear
complexity <= n**2. A single finite-prefix complexity > n**2 refutes
that claim for the recorded (N, a). No asymptotic claim follows.
Use 4*n**2 samples, sizes 16/20/24/28/32, three generated semiprimes
per size, four uniformly sampled unit bases per semiprime. Seed 1001.
Run with: timeout 60s python3 research/hypotheses/W001-orders-screen.py
Only stdout is written. Internal time cap: 55 seconds.
"""

import json
import math
import random
import time


def prime(x):
    return x >= 2 and all(x % d for d in range(2, math.isqrt(x) + 1))


def gen_prime(bits, rng):
    while True:
        x = rng.randrange(1 << (bits - 1), 1 << bits) | 1
        if prime(x):
            return x


def bm(bits):
    c = b = 1
    length = 0
    last = -1
    history = 0
    for i, bit in enumerate(bits):
        history = (history << 1) | bit
        if (c & history).bit_count() & 1:
            old = c
            c ^= b << (i - last)
            if 2 * length <= i:
                length = i + 1 - length
                b = old
                last = i
    return length, c


def profile(N, a):
    n = N.bit_length()
    s = n * n
    values = []
    value = 1
    for _ in range(4 * s):
        values.append(value)
        value = value * a % N
    lengths = [bm((v >> j & 1 for v in values))[0] for j in range(n)]
    return dict(N=N, a=a, n=n, cutoff=s, samples=len(values),
                min_L=min(lengths), max_L=max(lengths),
                bits_over_cutoff=sum(L > s for L in lengths))


def main():
    start = time.monotonic()
    rng = random.Random(1001)
    # Small independently recognizable recurrence checks.
    assert bm([0] * 20)[0] == 0
    assert bm([1] * 20)[0] == 1
    assert bm([0, 1] * 10)[0] == 2
    lfsr = [1, 0, 0]
    for _ in range(30):
        lfsr.append(lfsr[-3] ^ lfsr[-1])
    assert bm(lfsr)[0] == 3
    rows = []
    for n in (16, 20, 24, 28, 32):
        for instance in range(3):
            while True:
                p = gen_prime(n // 2, rng)
                q = gen_prime(n // 2, rng)
                N = p * q
                if p != q and N.bit_length() == n:
                    break
            for base_index in range(4):
                if time.monotonic() - start > 55:
                    print(json.dumps(dict(status="censored", rows=rows,
                                          elapsed=time.monotonic() - start)))
                    return
                while True:
                    a = rng.randrange(2, N)
                    if math.gcd(a, N) == 1:
                        break
                row = profile(N, a)
                row.update(instance=instance, base_index=base_index)
                rows.append(row)
    by_size = []
    for n in (16, 20, 24, 28, 32):
        group = [r for r in rows if r["n"] == n]
        by_size.append(dict(n=n, trials=len(group),
                            refuted=sum(r["bits_over_cutoff"] > 0 for r in group),
                            min_maxL=min(r["max_L"] for r in group),
                            max_maxL=max(r["max_L"] for r in group)))
    print(json.dumps(dict(status="complete", seed=1001,
                          elapsed=time.monotonic() - start,
                          by_size=by_size, rows=rows), sort_keys=True))


if __name__ == "__main__":
    main()
