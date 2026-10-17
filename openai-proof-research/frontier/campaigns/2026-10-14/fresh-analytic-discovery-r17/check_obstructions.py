"""MIT License; Copyright (c) 2026 Myeongjin Kang.

Exact finite checks of two diagnostic constructions, not a theorem verifier.
The general arguments are in interface-obstructions.md.
"""
from fractions import Fraction
from itertools import product, combinations


def check_chain(n):
    assignments = [a for a in product((0, 1), repeat=n)
                   if all(sum(a[i:i + 4]) == 2 for i in range(n - 3))]
    assert len(assignments) == 6
    for i in range(n - 4):
        assert all(a[i] == a[i + 4] for a in assignments)
    for i in range(n - 3):
        for j, k in combinations(range(i, i + 4), 2):
            assert sum(Fraction(a[j] != a[k], 4) for a in assignments) == 1
    for i in range(n - 2):
        trace = {b: sum(Fraction(a[i:i + 3] == b, 4) for a in assignments)
                 for b in product((0, 1), repeat=3)}
        assert all(m == (0 if sum(b) in (0, 3) else Fraction(1, 4))
                   for b, m in trace.items())


def check_coordinate_updates(steps):
    values = [[Fraction(0) for _ in range(steps)] for _ in range(3)]
    for t in range(steps):
        for coordinate in range(steps):
            i, j = (0, 1) if coordinate == t else (1, 2)
            average = (values[i][coordinate] + values[j][coordinate]) / 2
            perturbation = int(coordinate == t)
            values[i][coordinate] = average + perturbation
            values[j][coordinate] = average - perturbation
        assert all(sum(values[i][j] for i in range(3)) == 0
                   for j in range(steps))
        assert sum(abs(x) for x in values[0]) == t + 1


if __name__ == '__main__':
    for n in (5, 6, 9, 12):
        check_chain(n)
    check_coordinate_updates(24)
    print('Exact finite diagnostics passed; no full closure theorem tested.')
