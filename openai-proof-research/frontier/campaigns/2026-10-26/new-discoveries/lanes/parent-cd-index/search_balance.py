#!/usr/bin/env python3
"""Exact source-recursion search for Mahajan's contextual balance claims.

This is exploratory computation, not a Lean source bridge or novelty proof.
Every integer coefficient is generated from the actual G(c)=d,G(d)=cd
derivation and the Boolean cd-index recursion in source Proposition2.
"""
import argparse
from collections import defaultdict
from functools import lru_cache
import json
from math import comb


@lru_cache(None)
def beta_by_deletion(xs):
    if xs == (0,):
        return 1
    total = 0
    for i, x in enumerate(xs):
        if x:
            total += beta_by_deletion(xs[:i] + (x - 1,) + xs[i + 1:])
    for i in range(len(xs) - 1):
        total += beta_by_deletion(xs[:i] + (xs[i] + xs[i + 1] + 1,) + xs[i + 2:])
    return total


def next_index(coefficients):
    result = defaultdict(int)
    for xs, count in coefficients.items():
        # Append c.
        result[xs[:-1] + (xs[-1] + 1,)] += count
        # G(c)=d replaces a c in a run by a new separator d.
        for i, x in enumerate(xs):
            for before in range(x):
                result[xs[:i] + (before, x - before - 1) + xs[i + 1:]] += count
        # G(d)=cd increments the run before that d.
        for i in range(len(xs) - 1):
            result[xs[:i] + (xs[i] + 1,) + xs[i + 1:]] += count
    return dict(result)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=24)
    args = parser.parse_args()
    coefficients = {(0,): 1}
    result = {"source": "Mahajan math/0211390v1 Proposition2; Section7 Conjectures3/4",
              "credit": 0, "levels": [], "conjecture3_violation": None}
    for degree in range(args.degree + 1):
        # Independent source S-deletion recurrence; also exact one-d formula.
        if degree <= 14:
            assert all(beta_by_deletion(xs) == count for xs, count in coefficients.items())
        for xs, count in coefficients.items():
            if len(xs) == 2:
                assert count == comb(xs[0] + xs[1] + 2, xs[0] + 1) - 1
        checks = 0
        for xs, count in coefficients.items():
            for i, a in enumerate(xs):
                for j in range(i + 1, len(xs)):
                    b = xs[j]
                    if abs(a - b) < 2:
                        continue
                    ys = list(xs)
                    direction = 1 if a > b else -1
                    ys[i] -= direction
                    ys[j] += direction
                    balanced = coefficients[tuple(ys)]
                    checks += 1
                    if balanced <= count:
                        result["conjecture3_violation"] = {
                            "degree": degree, "unbalanced": xs, "value": count,
                            "balanced_pair": ys, "balanced_value": balanced,
                            "positions": [i, j],
                            "qualification": "Violation of strong pair claim only; weaker balanced-list claim needs separate check."}
                        print(json.dumps(result, indent=2))
                        return
        result["levels"].append({"degree": degree, "coefficients": len(coefficients),
                                 "strict_pair_balance_checks": checks})
        print(f"degree{degree}: coefficients{len(coefficients)}, checks{checks}, no violation", flush=True)
        coefficients = next_index(coefficients)
    result["status"] = "no strong-pair violation in finite search; no universal proof or discovery credit"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
