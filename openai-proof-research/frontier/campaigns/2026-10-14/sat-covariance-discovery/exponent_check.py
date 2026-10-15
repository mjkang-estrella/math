#!/usr/bin/env python3
"""Arithmetic audit of the exponents in proofs.md.

This file does not sample clauses, simulate satisfiability, or test a
central limit theorem. It checks only the powers obtained from the
martingale-expansion and Markov bounds written in proofs.md.
"""

from __future__ import annotations

import math


def post_exponent(k: int) -> tuple[float, str]:
    """Exponent of n in the upper bound for n * (E[S^4])^{1/2}.

    r = k - 1. The bound uses P(|T-mean| >= t) <= C n^{r/2} / t^r and
    |E[M_i M_j M_k^2]| <= C P(T >= k)^{(r-4)/r} for r > 4.
    """
    r = k - 1
    if r < 4:
        return math.inf, "no fourth moment"
    if r == 4:
        # theta = 0; |E[S_<k^2 M_k^2]| <= C (k-s)^2; sum_k O(n^2) = O(n^3)
        return 1 + 3 / 2, "r=4 absolute count"
    # Far triple density: t^2 * (n^{r/2} / t^r)^theta = n^{(r-4)/2} t^{6-r}
    # summed from t ~ n^{1/2} to t ~ n, plus the window O(w^3) = O(n^{3/2} polylog).
    if r > 7:
        # integral of t^{6-r} is lower-endpoint dominated; product is n^{3/2}
        return 1 + 3 / 4, "r>7 lower-endpoint"
    if r == 7:
        # harmonic far sum n^{3/2} log n, window n^{3/2} (log n)^6
        return 1 + 3 / 4, "r=7 harmonic"
    if r == 6:
        # t^2 * n / t^2 = n, summed over Theta(n) indices
        return 1 + 1, "r=6 flat"
    if r == 5:
        # t^2 * n^{1/2} / t = n^{1/2} t, summed through t ~ n gives n^{5/2}
        return 1 + 5 / 4, "r=5 upper-endpoint"
    raise AssertionError(r)


def far_kappa_exponent(k: int) -> tuple[float, str]:
    """Exponent of n in sum_{t >= w} E[kappa^2] for the far region."""
    r = k - 1
    if r < 4:
        return math.inf, "no fourth moment"
    if r == 4:
        return 2.0, "theta=0, Theta(n) indices times O(n)"
    # E[kappa^2] <= C n^{r/4} / t^{(r-4)/2}
    # r>6: integral from w ~ n^{1/2} converges, total exponent 3/2
    if r > 6:
        return 1.5, "r>6"
    if r == 6:
        return 1.5, "r=6 harmonic"
    if r == 5:
        # n^{5/4} * sum_{t<=n} t^{-1/2} has exponent 5/4 + 1/2
        return 1.75, "r=5"
    raise AssertionError(r)


def fourth_moment_only_post_exponent(k: int) -> float | None:
    """Weaker bound that Markov-controls the tail by the fourth moment only.

    Recorded so the r-moment threshold k >= 8 is not confused with this one.
    theta = (r-4)/r. Far sum of t^2 (n^2 / t^4)^theta is upper-endpoint
    dominated when theta < 3/4, giving E[S^4] = O(n^{3-2 theta}) and
    n (E[S^4])^{1/2} of order n^{(5-2 theta)/2}.
    """
    r = k - 1
    if r <= 4:
        return None
    theta = (r - 4) / r
    if theta < 0.75:
        return (5 - 2 * theta) / 2
    return 1.75


def main() -> None:
    print("k  r   theta     post_eta  far_eta  fourth_only_post  note")
    for k in range(4, 31):
        r = k - 1
        theta = None if r <= 4 else (r - 4) / r
        post, note = post_exponent(k)
        far, far_note = far_kappa_exponent(k)
        weak = fourth_moment_only_post_exponent(k)
        theta_s = "  -- " if theta is None else f"{theta:7.4f}"
        weak_s = "   --  " if weak is None else f"{weak:7.4f}"
        print(
            f"{k:2d} {r:2d} {theta_s}  {post:7.4f}  {far:7.4f}  {weak_s}        {note}; far {far_note}"
        )
        if k >= 8:
            assert post < 2.0, (k, post)
            assert far < 2.0, (k, far)
        if k == 7:
            assert post == 2.0
        if k == 6:
            assert abs(post - 2.25) < 1e-12
        if k == 9:
            assert abs(theta - 0.5) < 1e-12
            assert abs(post - 1.75) < 1e-12
            assert abs(weak - 2.0) < 1e-12
        if k == 10:
            assert weak is not None and abs(weak - 35 / 18) < 1e-12
            assert abs(post - 1.75) < 1e-12
        if k == 17:
            assert theta is not None and abs(theta - 0.75) < 1e-12

    # Closed-form majorants, not a clause simulation.
    # Window contribution to E[S^4] is at most order w^3.
    # Far contribution is at most order n^{(r-4)/2} * int_w^n t^{6-r} dt.
    # The ratio n (E[S^4])^{1/2} / n^2 tends to 0 for k >= 8 because it is
    # O((ln n)^3 n^{-1/4}). At moderate n the logarithm still dominates.
    def majorants(n: int, k: int) -> tuple[float, float, float]:
        r = k - 1
        w = math.ceil(math.sqrt(n) * (math.log(n) ** 2))
        window = float(w**3)
        gamma = (r - 4) / 2.0
        power = 6 - r
        if power == -1:
            integral = math.log(n / w)
        else:
            integral = (n ** (power + 1) - w ** (power + 1)) / (power + 1)
        far = (n**gamma) * max(integral, 0.0)
        return window, far, w

    for n in (10**6, 10**12, 10**24):
        log_ratio = (math.log(n) ** 3) / (n**0.25)
        print(f"n={n} (ln n)^3/n^(1/4)={log_ratio:.6e}")
        for k in (7, 8, 12):
            window, far, w = majorants(n, k)
            # Unit implicit constants. The k>=8 little-o is the window ratio.
            window_ratio = n * math.sqrt(window) / n**2
            far_ratio = n * math.sqrt(far) / n**2 if far > 0 else 0.0
            print(
                f"  k={k} w={w} window_ratio={window_ratio:.6e} "
                f"far_ratio={far_ratio:.6e}"
            )
    # Asymptotic assertions. The little-o is (ln n)^3 n^{-1/4} -> 0, which is
    # still larger than 1 at n = 10^6 and smaller than 1 by n = 10^24.
    assert (math.log(10**6) ** 3) / (10**6) ** 0.25 > 1
    assert (math.log(10**24) ** 3) / (10**24) ** 0.25 < 1
    previous = None
    for n in (10**24, 10**30, 10**36):
        window, far, _ = majorants(n, 8)
        ratio = n * math.sqrt(window + far) / n**2
        assert ratio < 1.0, (n, ratio)
        if previous is not None:
            assert ratio < previous
        previous = ratio
    # At k=7 the far majorant is order n^2, so its ratio stays order 1.
    for n in (10**24, 10**36):
        _w, far, _ = majorants(n, 7)
        far_ratio = n * math.sqrt(far) / n**2
        assert far_ratio > 0.1, (n, far_ratio)
    print("exponent checks passed")


if __name__ == "__main__":
    main()
