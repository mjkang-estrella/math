#!/usr/bin/env python3
"""Exact finite checks of the proposed general proof; not a universal proof."""
from fractions import Fraction as F
from pathlib import Path
import json
import random


def main():
    rng = random.Random(347947)
    cases = []
    for d in range(3, 31):
        m, k = d-3, 2*d-5
        for j in range(30):
            w = [rng.randrange(0, 25) for _ in range(d)]
            if j % 3 == 0:
                w[0] = rng.randrange(1, 20)*d
            den = sum(t*t for t in w)
            if not den:
                w[0], den = 1, 1
            p = [F(t*t, den) for t in w]
            a = sorted([F(x+y, 2) for x in p for y in p], reverse=True)
            g = sorted([F(x*y, den) for x in w for y in w], reverse=True)
            aa, gg, pm = sum(a[:k]), sum(g[:k]), max(p)
            assert gg*gg <= k
            assert (gg-pm)**2 <= (k-1)*(1-pm*pm)
            if pm <= F(2, 3):
                assert aa <= F(4*m+7, 6)
            else:
                assert aa <= 1+m*pm
            assert aa+gg < d
        cases.append({"d": d, "probability_vectors": 30, "all_checks": "PASS exact Fraction on square-weight inputs"})
    witness = []
    for m in range(2, 101):
        d, den = m+3, 4*m*m+m
        aa = F((2*m+3)*4*m*m+2*m, 2*den)
        gg = F(8*m*m+1, den)
        gap = aa+gg-d
        assert gap == F((m-1)**2, den) and gap > 0
        if m <= 15:
            w = [2*m]+[1]*m+[0, 0]
            p = [F(t*t, den) for t in w]
            a = sorted([F(x+y, 2) for x in p for y in p], reverse=True)
            g = sorted([F(x*y, den) for x in w for y in w], reverse=True)
            assert sum(a[:2*m+2]) == aa and sum(g[:2*m+2]) == gg
        witness.append({"m": m, "d": d, "gap": str(gap)})
    result = {"status": "PASS: exact finite checks, not universal proof", "seed": 347947,
              "cases": cases, "uniform_sharpness_checks": witness, "credit": 0}
    Path(__file__).with_name("exact-bound-check.json").write_text(json.dumps(result, indent=2)+"\n")
    print("PASS", sum(x["probability_vectors"] for x in cases), "probability vectors;",
          len(witness), "sharpness-family parameters")


if __name__ == "__main__":
    main()
