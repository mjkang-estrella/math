#!/usr/bin/env python3
"""Finite scalar-pattern diagnostic only; not a mathematical gate."""
import itertools
import json


def coefficients(parts):
    roles = dict(Tp="X", Tm="X", S="X", Z="A", Y="A", Up="U",
                 Um="U", W="U", DM="D", DG="D", FT="F", FM="F", FG="F")
    counts = {name: parts.count(name) for name in roles}
    total = len(parts)
    result = [5 * sum(counts[s] for s in roles if roles[s] == r) - total
              for r in ("X", "A", "U", "D", "F")]
    result += [counts["Tp"] + counts["Tm"] - counts["FT"],
               counts["Z"] - counts["FT"] - counts["FM"],
               counts["Up"] + counts["Um"] - counts["FT"] - counts["FM"],
               counts["DM"] - counts["FT"] - counts["FM"],
               counts["Tm"] - counts["Um"]]
    return result


def main():
    types = {s: (s,) for s in ("Tp", "Tm", "S", "Z", "Y", "DM", "DG")}
    types.update(Vpt=("Up", "FT"), Vmt=("Um", "FT"),
                 Vpm=("Up", "FM"), Vwg=("W", "FG"))
    expected = {tuple(sorted(t)) for t in [
        ("Tp", "Z", "DM", "Vpt"), ("Tm", "Z", "DM", "Vmt"),
        ("S", "Z", "DM", "Vpm"), ("S", "Y", "DG", "Vwg")]}
    actual = set()
    tested = 0
    max_coefficient = 0
    for names in itertools.combinations_with_replacement(sorted(types), 4):
        parts = [part for name in names for part in types[name]]
        vector = coefficients(parts)
        max_coefficient = max(max_coefficient, *map(abs, vector))
        score = sum(value * 100 ** j for j, value in enumerate(vector))
        assert (score == 0) == all(value == 0 for value in vector)
        if score == 0:
            actual.add(names)
        tested += 1
    assert actual == expected
    print(json.dumps({"purpose": "finite diagnostic, not mathematical gate",
                      "four_item_multisets_tested": tested,
                      "zero_score_patterns": sorted(actual),
                      "max_abs_coefficient": max_coefficient,
                      "expected_patterns_match": True}, indent=2))


if __name__ == "__main__":
    main()
