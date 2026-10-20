#!/usr/bin/env python3
# Reviewer round2: exact rational spot-checks for Proposition B's two-bracket identity
# and for the expectation E exp(-W^+/alpha - W^-/beta) via the Lemma-7 density.
# Independent of the author's code. Fractions only.
from fractions import Fraction as Fr
import sys

sys.dont_write_bytecode = True


def partials(b):
    """A_j = prod_{i != j} c_j/(c_j - c_i) for distinct nonzero entries."""
    w = [c for c in b if c != 0]
    A = []
    for j, cj in enumerate(w):
        a = Fr(1)
        for i, ci in enumerate(w):
            if i != j:
                a *= Fr(cj) / (cj - ci)
        A.append(a)
    return w, A


def stats(b):
    w, A = partials(b)
    p = sum((a for a, c in zip(A, w) if c > 0), Fr(0))
    P = sum((a * c for a, c in zip(A, w) if c > 0), Fr(0))
    N = sum((a * (-c) for a, c in zip(A, w) if c < 0), Fr(0))
    return p, P, N


def Dfun(b):
    s = sorted(b)
    m = len(s)
    return sum((2 * (i + 1) - m - 1) * s[i] for i in range(m))


def exp_laplace(b, alpha, beta):
    """E exp(-W^+/alpha - W^-/beta) from the exact density (Lemma 7), integrated in
    closed form: each summand contributes A_j*alpha/(c_j+alpha) for c_j>0 and
    A_j*beta/(|c_j|+beta) for c_j<0."""
    w, A = partials(b)
    tot = Fr(0)
    for a, c in zip(A, w):
        if c > 0:
            tot += a * alpha / (c + alpha)
        else:
            tot += a * beta / ((-c) + beta)
    return tot


def check(b, alpha, n=4):
    beta = 2 - alpha
    p, P, N = stats(b)
    d = Dfun(b) / Fr(2 * (n + 1))
    psi = (1 + d) * exp_laplace(b, alpha, beta)
    # two-bracket identity, only meaningful for 0 < p < 1
    info = {}
    if 0 < p < 1:
        A_ = P / p
        B_ = N / (1 - p)
        bound = p * alpha / (alpha + A_) + (1 - p) * beta / (beta + B_)
        Q = 1 - (1 + d) * bound
        lhs = (alpha + A_) * (beta + B_) * Q / (alpha * beta)
        rhs = (P / alpha + N / beta - d) + (A_ * B_ / (alpha * beta)) * (
            1 - d * (p * p * alpha / P + (1 - p) ** 2 * beta / N))
        info["identity_holds"] = (lhs == rhs)
        info["first_bracket_nonneg"] = (P / alpha + N / beta - d) >= 0
        s1 = d * p * p * alpha / P
        s2 = d * (1 - p) ** 2 * beta / N
        info["second_bracket_strict"] = (s1 < alpha / 2) and (s2 <= beta / 2)
    info["psi"] = psi
    info["psi_lt_1"] = psi < 1
    return info


def main():
    ok = True
    # samples: mixed signs, degenerate (repeated) knots, zeros, pure positive, pure negative
    # samples: mixed signs, near-degenerate distinct knots, zeros, pure positive, pure negative.
    # (Repeated nonzero entries are outside Lemma 7's distinctness hypothesis; that case is
    # covered in the review by the continuity argument, not by this spot-check.)
    samples = [
        ([Fr(1), Fr(-1), Fr(2), Fr(-3)], Fr(1)),
        ([Fr(1), Fr(1001, 1000), Fr(501, 500), Fr(-2)], Fr(1, 2)),
        ([Fr(2), Fr(0), Fr(-1), Fr(0)], Fr(3, 2)),
        ([Fr(3), Fr(-1), Fr(-1001, 1000), Fr(-999, 1000)], Fr(7, 4)),
        ([Fr(1), Fr(2), Fr(3), Fr(4)], Fr(1)),      # p = 1
        ([Fr(-1), Fr(-2), Fr(-3), Fr(-4)], Fr(1)),  # p = 0
        ([Fr(1), Fr(1001, 1000), Fr(999, 1000), Fr(1002, 1000)], Fr(2, 3)),  # d tiny, p = 1
        ([Fr(5), Fr(-1), Fr(1), Fr(-2)], Fr(1, 3)),
        ([Fr(1, 7), Fr(-3, 11), Fr(2, 5), Fr(-1, 13)], Fr(9, 7)),
    ]
    for b, alpha in samples:
        info = check(b, alpha)
        good = info["psi_lt_1"] and info.get("identity_holds", True) \
            and info.get("first_bracket_nonneg", True) and info.get("second_bracket_strict", True)
        ok &= good
        print("b =", [str(x) for x in b], "alpha =", alpha, "Psi =", float(info["psi"]),
              {k: v for k, v in info.items() if k != "psi"}, "OK" if good else "FAIL")
    print("PROPOSITION B SPOT-CHECK", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
