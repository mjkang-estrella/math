#!/usr/bin/env python3
"""Exact exploratory test of 2602.20536 formulas (12), (14), (17)-(19)."""
import json
import random
import time
from pathlib import Path
import numpy as np


def pad(v, n):
    # np.pad inserts NumPy scalar zeros even into object arrays; subsequent
    # arithmetic can then silently use fixed-width NumPy integers. Normalize
    # every entry to a genuine arbitrary-precision Python int instead.
    return np.array(list(map(int, v)) + [0] * (n - len(v)), dtype=object)


def add(a, b):
    n = max(len(a), len(b))
    return pad(a, n) + pad(b, n)


def shift(v):
    return np.concatenate((np.array([0], dtype=v.dtype), v))


def apply(letter, n, d):
    qn = shift(n)
    if letter == 'R':
        return add(qn, d), d
    return qn, add(qn, d)


def unimodal(v):
    falling = False
    for i in range(len(v) - 1):
        if v[i] > v[i + 1]:
            falling = True
        elif falling and v[i] < v[i + 1]:
            return False
    return True


def triple(n, d):
    degree = max(len(n), len(d))
    ni, di = pad(d, degree)[::-1], pad(n, degree)[::-1]
    a = add(shift(np.convolve(n, ni)), np.convolve(d, di))
    left, right = np.convolve(n, di), np.convolve(d, ni)
    b = pad(left, max(len(left), len(right))) - pad(right, max(len(left), len(right)))
    c = add(shift(np.convolve(n, n)), np.convolve(d, d))
    return a, b, c


def check(word, n, d):
    if sum(n) <= sum(d):
        return None
    abc = triple(n, d)
    m, den = int(sum(n)), int(sum(d))
    assert [int(sum(v)) for v in abc] == [2 * m * den, m*m-den*den, m*m+den*den]
    assert all(all(int(x) >= 0 for x in v) for v in abc)
    for name, v in zip('ABC', abc):
        if not unimodal(v):
            return {'word': word, 'm': m, 'n': den, 'polynomial': name,
                    'numerator': list(map(int, n)), 'denominator': list(map(int, d)),
                    'coefficients': list(map(int, v))}
    return None


def main():
    started = time.monotonic()
    checked = 0
    hit = None
    states = [('R', np.array([1], dtype=object), np.array([1], dtype=object))]
    for depth in range(1, 17):
        for word, n, d in states:
            if sum(n) > sum(d):
                checked += 1
                hit = check(word, n, d)
                if hit:
                    break
        if hit:
            break
        states = [(l + w, *apply(l, n, d)) for w, n, d in states for l in 'RL']
    rng = random.Random(20261026)
    random_count = 0
    if not hit:
        for trial in range(10000):
            length = rng.randint(17, 100)
            word = 'R' + ''.join(rng.choice('RL') for _ in range(length - 2)) + 'R'
            n, d = np.array([0], dtype=object), np.array([1], dtype=object)
            for l in reversed(word):
                n, d = apply(l, n, d)
            checked += 1
            random_count += 1
            hit = check(word, n, d)
            if hit:
                break
    result = {'source': '2602.20536 latest PDF, exact formulas 12,14,17-19',
              'arithmetic': 'Python arbitrary-precision integers via NumPy object arrays',
              'all_binary_words_length_at_most': 16, 'random_words_tested': random_count,
              'random_max_length': 100, 'triples_checked': checked, 'hit': hit,
              'elapsed_seconds': time.monotonic() - started,
              'qualification': 'Exploratory finite search only; no discovery credit or universal proof.'}
    Path('pythagorean-screen.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
