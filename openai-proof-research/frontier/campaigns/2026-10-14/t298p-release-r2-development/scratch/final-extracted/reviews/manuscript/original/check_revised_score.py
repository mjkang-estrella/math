#!/usr/bin/env python3
"""Independent r4 exact finite score/entry diagnostics; not an analytic proof."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import product
import json


@cache
def moment(word):
    if not word:
        return 1
    if len(word) % 2:
        return 0
    # Noncrossing pairings of two free variance-one semicircular letters.
    return sum(moment(word[1:j]) * moment(word[j+1:])
               for j in range(1, len(word), 2) if word[j] == word[0])


def derivative(word):
    return [(word[:j], word[j+1:]) for j in range(len(word)) if word[j] == 's']


def score(u, v):
    ans = Counter({v + 's' + u: 1})
    for left, right in derivative(u):
        ans[v + right] -= moment(left)
    for left, right in derivative(v):
        ans[left + u] -= moment(right)
    return ans


def pair(poly, word):
    return sum(coef * moment(term + word) for term, coef in poly.items())


def insertion(u, v, p):
    return sum(moment(left + u) * moment(v + right) for left, right in derivative(p))


def words(n):
    return [''.join(w) for length in range(n+1) for w in product('st', repeat=length)]


def emul(x, y):
    return (x[0], y[1]) if x is not None and y is not None and x[1] == y[0] else None


def etrace(x, k):
    return Q(int(x is not None and x[0] == x[1]), k)


def main():
    scalar = 0
    for u, v, p in product(words(3), words(3), words(5)):
        c = score(u, v)
        actual = insertion(u, v, p)
        assert pair(c, p) == actual, (u, v, p)
        # All coefficients here are real; the Hilbert vector has reversed words.
        h = {term[::-1]: coef for term, coef in c.items()}
        hilbert_pair = sum(coef * moment(term[::-1] + p) for term, coef in h.items())
        assert hilbert_pair == actual
        scalar += 1
    matrix = 0
    for k in (2, 3):
        for b, c, i, j in product(range(k), repeat=4):
            # Directly multiply the matrix units on BOTH legs of the insertion.
            direct = sum(etrace(emul((i,j), (ell,b)), k) * etrace((c,ell), k)
                         for ell in range(k))
            score_factor = Q(1, k) * etrace(emul((c,b), (i,j)), k)
            assert direct == score_factor
            for u, v, p in product(words(2), words(2), words(3)):
                assert direct * insertion(u, v, p) == score_factor * pair(score(u,v), p)
                matrix += 1
    witness = {'u':'t', 'v':'1', 'P':'ts', 'inserted':insertion('t','','ts'),
               'revised':pair(score('t',''), 'ts'), 'old_unconverted':moment('tsts')}
    assert witness['inserted'] == witness['revised'] == 1 and witness['old_unconverted'] == 0
    # Matrix transpose and normalization negative controls, b=0,c=1,P=E_01*s.
    right = Q(1,2) * etrace(emul((1,0),(0,1)),2)
    wrong_transpose = Q(1,2) * etrace(emul((0,1),(0,1)),2)
    wrong_scale = etrace(emul((1,0),(0,1)),2)
    assert right == Q(1,4) and wrong_transpose == 0 and wrong_scale == Q(1,2)
    # Derivative correction is indispensable: u=s, v=1, P=1.
    assert insertion('s','','') == pair(score('s',''), '') == 0
    assert moment('ss') == 1
    print(json.dumps({'scope':'finite semicircular and matrix-unit identities only',
                      'scalar_and_hilbert_cases':scalar, 'matrix_cases':matrix,
                      'witness':witness,
                      'negative_controls':['old unconverted bilinear expression',
                                           'matrix transpose', 'missing 1/k',
                                           'missing differentiated coefficient']}, indent=2))


if __name__ == '__main__':
    main()
