#!/usr/bin/env python3
"""Search the still-open weaker balanced-list claim, not the posted pair failure.

All lists at each searched total degree are tested with contexts of length at
most one on each side. Three-entry and longer middle lists are included.
"""
import argparse
from itertools import combinations
import json
from search_balance import next_index


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=29)
    args = parser.parse_args()
    coefficients = {(0,): 1}
    levels = []
    for degree in range(args.degree + 1):
        groups = {}
        for xs, value in coefficients.items():
            for before in range(2):
                for after in range(2):
                    length = len(xs) - before - after
                    if length < 3:
                        continue
                    middle = xs[before:len(xs)-after if after else len(xs)]
                    key = (xs[:before], xs[len(xs)-after:] if after else (), length)
                    balanced = max(middle) - min(middle) <= 1
                    if key not in groups:
                        groups[key] = [value, middle, value if balanced else -1, middle if balanced else None]
                    else:
                        row = groups[key]
                        if value > row[0]:
                            row[0], row[1] = value, middle
                        if balanced and value > row[2]:
                            row[2], row[3] = value, middle
        for key, (maxvalue, middle, balancedvalue, balancedmiddle) in groups.items():
            assert balancedvalue >= 0
            if maxvalue > balancedvalue:
                result = {"status": "candidate weak-list violation; not yet a theorem, Lean bridge or novelty finding",
                          "degree": degree, "context_left": key[0], "context_right": key[1],
                          "middle": middle, "value": maxvalue,
                          "best_balanced_middle": balancedmiddle, "best_balanced_value": balancedvalue,
                          "credit": 0, "earlier_levels": levels}
                print(json.dumps(result, indent=2))
                return
        levels.append({"degree": degree, "coefficients": len(coefficients),
                       "context_degree_length_groups": len(groups)})
        print(f"degree{degree}: {len(coefficients)}coefficients,{len(groups)}groups,no weak-list violation", flush=True)
        coefficients = next_index(coefficients)
    print(json.dumps({"status": "no weak-list violation in finite restricted-context search",
                      "levels": levels, "credit": 0}, indent=2))


if __name__ == "__main__":
    main()
