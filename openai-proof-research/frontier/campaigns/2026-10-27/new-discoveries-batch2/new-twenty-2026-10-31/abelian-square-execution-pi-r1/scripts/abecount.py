#!/usr/bin/env python3
"""Exact distinct abelian-square factor counter (literal strings, not Parikh classes).

An abelian square is a factor x+y, |x|=|y|, x an anagram of y (equal letter counts).
Distinctness is on literal factor STRINGS: two occurrences count once iff the
substring (length + content) is identical.

Counter A (fast): prefix count arrays; square iff equal length and equal letter
counts on both halves; distinct set keyed by (length, tuple(chars)).
Counter B (slow, independent): brute-force over all factor pairs.

Self-test: random words over small alphabets, A vs B must agree exactly.
"""
import random, sys


def count_asq_A(w):
    """Distinct abelian-square factors of string w, literal-string dedup."""
    n = len(w)
    # prefix counts per letter
    letters = sorted(set(w))
    idx = {c: i for i, c in enumerate(letters)}
    P = [[0] * (len(letters)) for _ in range(n + 1)]
    for i, ch in enumerate(w):
        row = P[i][:]; row[idx[ch]] += 1; P[i + 1] = row
    seen = set()
    for a in range(n):
        for b in range(a + 2, n + 1, 2):        # even length >= 2
            m = (a + b) // 2
            left = P[m]; right = P[b]; base = P[a]
            ok = True
            for k in range(len(letters)):
                if (left[k] - base[k]) != (right[k] - left[k]):
                    ok = False; break
            if ok:
                seen.add((b - a, w[a:b]))
    return len(seen), seen


def count_asq_B(w):
    """Independent brute force: every split of every factor."""
    n = len(w)
    seen = set()
    for i in range(n):
        for j in range(i + 1, n + 1):
            f = w[i:j]
            h = len(f)
            if h % 2:
                continue
            x, y = f[:h // 2], f[h // 2:]
            if sorted(x) == sorted(y):
                seen.add(f)
    return len(seen), seen


def selftest(trials=300, maxn=14, maxk=4, seed=20261105):
    rng = random.Random(seed)
    bad = 0
    for t in range(trials):
        n = rng.randint(1, maxn)
        k = rng.randint(1, min(maxn, max(2, maxk)))
        w = ''.join(rng.choice('abcd'[:k]) for _ in range(n))
        a, sa = count_asq_A(w)
        b, sb = count_asq_B(w)
        if a != b or {s for _, s in sa} != sb:
            bad += 1
            print('MISMATCH', w, a, b)
    print('selftest trials=%d mismatches=%d' % (trials, bad))
    return bad


if __name__ == '__main__':
    sys.exit(1 if selftest() else 0)
