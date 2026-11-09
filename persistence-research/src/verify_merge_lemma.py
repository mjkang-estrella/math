"""Exhaustive verification of the merge-monotonicity lemma (notes/theory.md, Lemma 4).

Claim: for equal-size digit multisets X, Y (digits 2..9) with sorted(X) < sorted(Y)
lexicographically and prod(X) == prod(Y), for EVERY digit multiset R (digits 2..9,
|R| <= 4): sort(R+X) < sort(R+Y) as numbers (same length, so lex on sorted digits).

If any counterexample existed, the replacement moves in Lemma 4 could backfire.
"""
from itertools import combinations_with_replacement as CwR
from math import prod

DIGITS = range(2, 10)


def sorted_num(ms: tuple) -> int:
    return int("".join(map(str, sorted(ms))))


def multisets(size):
    return list(CwR(DIGITS, size))


def main():
    tested = counterexamples = 0
    for k in (2, 3, 4):
        pairs = {}
        for X in multisets(k):
            pairs.setdefault(prod(X), []).append(sorted_num(X))
        for prods, reps in pairs.items():
            if len(reps) < 2:
                continue
            reps = sorted(set(reps))
            for i, sx in enumerate(reps):
                for sy in reps[i + 1:]:
                    # X = the multiset with sorted number sx (smaller), Y = sy
                    # replacement Y -> X must shrink the number for every R
                    for rsize in (0, 1, 2, 3, 4):
                        for R in multisets(rsize):
                            tested += 1
                            if sorted_num(R + tuple(int(c) for c in str(sx))) >= \
                               sorted_num(R + tuple(int(c) for c in str(sy))):
                                counterexamples += 1
                                print("COUNTEREXAMPLE:", prods, sx, sy, R)
    print(f"tested {tested} (X,Y,R) triples, counterexamples: {counterexamples}")
    assert counterexamples == 0


if __name__ == "__main__":
    main()
