#!/usr/bin/env python3
"""Bounded exact automata diagnostic; not a universal proof or gate. Read-only."""
from fractions import Fraction as F
from itertools import product
import json


def check():
    cases = 0
    for h, maxlen in [(2, 3), (3, 1)]:
        letters = range(1 << (h*h))
        for length in range(maxlen + 1):
            for word in product(letters, repeat=length):
                n = sum(all((word[j] >> (path[j]*h + path[j+1])) & 1
                            for j in range(length))
                        for path in product(range(h), repeat=length+1))
                alive = set(range(h))
                for r in word:
                    alive = {b for a in alive for b in range(h) if (r >> (a*h+b)) & 1}
                assert (n > 0) == bool(alive)
                q = h**(length+1)
                pa, pr = F(n, 2*q), F(1, 4*q)
                assert 0 < pa+pr <= 1
                a = pa/(pa+pr)
                assert a == F(2*n, 2*n+1)
                assert (a >= F(2, 3)) if n else (a == 0)
                cases += 1
    # Deliberately omit rejection survival coins on a length-three identity word.
    pa = F(2, 2*2**4)
    wrong_pr = F(1, 4*2)
    assert pa/(pa+wrong_pr) < F(2, 3)
    return {'exact_word_cases': cases, 'wrong_rejection_schedule_detected': True,
            'scope': 'h=2 length<=3 and h=3 length<=1; rational probability identities only',
            'mathematical_gate': False}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
