"""Heuristic calibration: how likely is a persistence-12 number, empirically?

Measures the persistence distribution of RANDOM L-digit numbers for growing L,
including the conditional distribution given a 0-free start. If the folk model
("chain dies by zero digit or shrink") is right, P(P(n) >= 12) should be
astronomically small at every L, and the *typical* persistence should follow
~4.44*log10(L) until the zero-wall cuts it to ~1.

Writes results/heuristic_calibration.md
"""
import random
import sys
from collections import Counter

sys.path.insert(0, "src")
from persistence import persistence, digit_product

rng = random.Random(20260214)


def random_ndigit(L):
    return rng.randrange(10 ** (L - 1), 10 ** L)


def main():
    rows = []
    for L in (10, 15, 20, 30, 45, 65, 95, 140, 200, 300):
        N = 200_000 if L <= 65 else 50_000
        hist = Counter()
        maxp, argmax = 0, 0
        for _ in range(N):
            n = random_ndigit(L)
            p = persistence(n)
            hist[p] += 1
            if p > maxp:
                maxp, argmax = p, n
        # conditional: start from a hand-made 0-free number (digits 1-9)
        hist0 = Counter()
        maxp0 = 0
        for _ in range(min(N, 50_000)):
            n = int("".join(rng.choice("123456789") for _ in range(L)))
            p = persistence(n)
            hist0[p] += 1
            maxp0 = max(maxp0, p)
        frac_ge11 = sum(v for k, v in hist0.items() if k >= 11) / max(1, sum(hist0.values()))
        rows.append((L, N, maxp, argmax, maxp0, frac_ge11, hist0.most_common(4)))
        print(f"L={L:4d} N={N}: maxP(all)={maxp}  maxP(0-free start)={maxp0}"
              f"  P(P>=11 | 0-free)={frac_ge11:.2e}  top0={hist0.most_common(3)}", flush=True)

    with open("results/heuristic_calibration.md", "w") as f:
        f.write("# Heuristic calibration (Monte Carlo)\n\n")
        f.write("Random L-digit integers; `0-free start` = random digits from {1..9}.\n\n")
        f.write("| L | N | max P (all) | max P (0-free start) | P(P>=11 \\| 0-free) |\n")
        f.write("|---|---|---|---|---|\n")
        for L, N, maxp, argmax, maxp0, frac, _ in rows:
            f.write(f"| {L} | {N} | {maxp} | {maxp0} | {frac:.2e} |\n")
        f.write("\nInterpretation: see notes/theory.md section 7. The conditional\n"
                "probability of reaching persistence >= 11 from a random 0-free start\n"
                "should collapse super-exponentially in L; extrapolation gives the\n"
                "expected total count of persistence-12 integers.\n")
    print("wrote results/heuristic_calibration.md")


if __name__ == "__main__":
    main()
