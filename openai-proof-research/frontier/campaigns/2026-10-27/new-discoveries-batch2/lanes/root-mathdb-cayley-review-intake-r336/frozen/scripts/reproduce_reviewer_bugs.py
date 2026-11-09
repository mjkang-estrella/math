#!/usr/bin/env python3
"""Preserved failures of this review (exact reproducers).

F1: first-appearance normalization is NOT an order-isomorphism invariant;
    it wrongly declares word 2211 to contain pattern 1122.
F2: comparing tuple normalize(...) == list p is always False; with a list
    pattern the containment predicate silently never fires.
F3 (candidate evidence, not rerun here): root-mathdb-breadth-intake-r332/
    frozen/work/decisive-cayley-validation.json contains a control run with
    "ok": false (the |Cay_n(112)| row counts equal Fubini totals, i.e. its
    contains() never fired) and decisive_cayley verify's "fubini5_check"
    enumerates only letters 1..4 (421, not 541). These are recorded
    artifacts, quoted in review.md; they do not affect the decisive counts,
    which this review rederived independently.

Exit code 0 iff all three preserved failures reproduce as documented.
"""
import itertools
import json
import os
import sys

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "work",
                   "preserved-failures.json")


def normalize_first_appearance(sub):
    rank = {}
    out = []
    for x in sub:
        if x not in rank:
            rank[x] = len(rank) + 1
        out.append(rank[x])
    return tuple(out)


def normalize_by_value(sub):
    rank = {v: i + 1 for i, v in enumerate(sorted(set(sub)))}
    return tuple(rank[x] for x in sub)


def main():
    R = {}

    # F1: 2211 normalized by first appearance equals (1,1,2,2) -> false positive
    w = (2, 2, 1, 1)
    R["F1_word"] = list(w)
    R["F1_first_appearance_norm"] = list(normalize_first_appearance(w))
    R["F1_value_norm"] = list(normalize_by_value(w))
    R["F1_pattern_1122"] = [1, 1, 2, 2]
    R["F1_false_positive"] = normalize_first_appearance(w) == (1, 1, 2, 2)
    R["F1_correct_conclusion"] = not (normalize_by_value(w) == (1, 1, 2, 2))
    assert R["F1_false_positive"] and R["F1_correct_conclusion"]

    # F2: tuple != list comparison silently disables the predicate
    R["F2_tuple_eq_list"] = (1, 1, 2, 2) == [1, 1, 2, 2]
    assert R["F2_tuple_eq_list"] is False

    # F3: quote candidate's recorded control failure (read-only)
    cand = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..",
                        "..", "root-mathdb-breadth-intake-r332", "frozen",
                        "work", "decisive-cayley-validation.json")
    with open(cand) as f:
        val = json.load(f)
    row112 = val["validations"][0]
    row13442 = val["validations"][2]
    R["F3_candidate_validation_112_row_ok"] = row112["ok"]
    R["F3_candidate_validation_112_detail"] = row112["detail"]
    R["F3_candidate_13442_14233_unequal_rows"] = [
        d for d in row13442["detail"] if not d["equal"]]
    assert row112["ok"] is False
    assert R["F3_candidate_13442_14233_unequal_rows"]

    with open(OUT, "w") as f:
        json.dump(R, f, indent=2)
    print(json.dumps(R, indent=2))
    print("PRESERVED FAILURES REPRODUCED", file=sys.stderr)


if __name__ == "__main__":
    main()
