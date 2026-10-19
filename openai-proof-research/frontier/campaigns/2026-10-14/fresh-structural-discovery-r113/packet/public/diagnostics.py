#!/usr/bin/env python3
"""Exact finite diagnostics only. No mathematical or contribution verdict."""
from fractions import Fraction as Q
from itertools import combinations, product
import json


def check(condition):
    if not condition:
        raise RuntimeError("finite diagnostic failed")


def statistic(state):
    return sum((1 if x % 2 == 0 else -1) * c for x, c in enumerate(state))


def run():
    moments = transitions = invariants = 0
    for d in (1, 2, 3):
        n = 2 ** d
        states = []
        for plus in combinations(range(n), n // 2):
            pos = set(plus)
            states.append(tuple(1 if x in pos else -1 for x in range(n)))
        check(sum(map(statistic, states)) == 0)
        check(Q(sum(statistic(x) ** 2 for x in states), len(states)) == Q(n*n, n-1))
        for state in states:
            for axis in range(1, d):
                for x in range(n):
                    if x & (1 << axis):
                        continue
                    changed = list(state)
                    y = x ^ (1 << axis)
                    changed[x], changed[y] = changed[y], changed[x]
                    check(statistic(changed) == statistic(state))
                    invariants += 1
            for p in (Q(1, 4), Q(1, 2), Q(3, 4)):
                mean = second = total = Q(0)
                for mask in product((0, 1), repeat=n//2):
                    changed = list(state)
                    for j, swapped in enumerate(mask):
                        if swapped:
                            changed[2*j], changed[2*j+1] = changed[2*j+1], changed[2*j]
                    weight = p ** sum(mask) * (1-p) ** (n//2-sum(mask))
                    f = statistic(changed)
                    total += weight
                    mean += weight * f
                    second += weight * f*f
                    transitions += 1
                check(total == 1)
                check(mean == (1-2*p)*statistic(state))
                check(0 <= second-mean*mean <= 8*n*p*(1-p))
                moments += 1
    coupling = factorials = 0
    for c in range(1, 21):
        for p in (Q(0), Q(1, 4), Q(1, 2), Q(3, 4), Q(1)):
            for size in range(c+1):
                check(1-(1-p/c)**size <= p*size/c)
                coupling += 1
        falling = 1
        for r in range(1, c+1):
            falling *= c-r+1
            check(falling >= Q(c, 3)**r)
            factorials += 1
    return {
        "status": "finite_diagnostics_only",
        "balanced_moment_cases": moments,
        "weighted_transitions": transitions,
        "other_coordinate_invariances": invariants,
        "stationary_variance_sizes": [2, 4, 8],
        "rainbow_coupling_cases": coupling,
        "weaker_falling_factorial_checks": factorials,
        "limits": "No all-d proof, no e-constant verification, no eligibility or acceptance gate."
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
