#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. MIT.
Finite exact arithmetic and runner controls, not an all-n crossing proof.
"""
from fractions import Fraction
from math import comb
from checked_run import failed


def hh(n):
    return (n//2)*((n-1)//2)*((n-2)//2)*((n-3)//2)//4


def target(n):
    return hh(n) - comb((n-1)//2, 2)


def ceiling(x):
    return -((-x.numerator)//x.denominator)


def main():
    sizes = list(range(2, 101)) + [10**12, 10**100]
    for s in sizes:
        n = 2*s+1
        bound = Fraction(2*hh(n-1)+(n-2)*(hh(n)-(n-3)//2), n)
        gap = Fraction((s-1)*(s-2), 2*(2*s+1))
        assert target(n)-bound == gap
        assert (gap >= 1) == (s >= 7)
        assert (ceiling(bound) == target(n)) == (s <= 6)
    assert target(15) == 420 and ceiling(Fraction(6285, 15)) == 419
    for n in list(range(2, 1001)) + [10**100, 10**100+1]:
        product = ((n+2)//2)*((n-1)//2)*((n-3)//2)*((n-4)//2)//4
        assert target(n) == product
    for m in list(range(4, 201)) + [10**100, 10**100+1]:
        for edges in [1, 2, 7, 10**50]:
            via_owh = (edges-1)*target(m+2) + 2*hh(m+1)
            closed = ((m+1)//2)*((m-1)//2)*((m-2)//2)*(edges*((m+4)//2)+(m-4)//2)//4
            assert via_owh == closed
    # The marker and exit-status paths are independent; both must reject.
    assert failed(0, 'SOME FAIL\n', '')
    assert failed(0, 'rank -> FAIL\n', '')
    assert failed(0, '', 'error: synthetic negative control')
    assert failed(9, 'ALL OK\n', '')
    assert not failed(0, 'ALL OK\n', '')
    print('PASS exact integer/Fraction formula checks, including 101-digit integers')
    print('PASS failure-output and nonzero-status runner controls')
    print('Finite support only; no drawing theorem or priority claim')


if __name__ == '__main__':
    main()
