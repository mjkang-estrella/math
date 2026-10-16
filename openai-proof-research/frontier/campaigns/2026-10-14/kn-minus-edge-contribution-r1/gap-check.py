#!/usr/bin/env python3
"""Exact gaps between classical counting bounds and the K_n-e formula.

Stdlib only. These identities support the contribution review. They are not a proof.
"""

from math import floor


def Z(n: int) -> int:
    return (
        floor(n / 2)
        * floor((n - 1) / 2)
        * floor((n - 2) / 2)
        * floor((n - 3) / 2)
        // 4
    )


def target(n: int) -> int:
    return (
        floor((n + 2) / 2)
        * floor((n - 1) / 2)
        * floor((n - 3) / 2)
        * floor((n - 4) / 2)
        // 4
    )


def owh_31(m: int) -> tuple[int, int]:
    """OWH Theorem 3.1, returned as numerator/denominator of the lower bound."""
    numer = 2 * Z(m - 1) + (m - 2) * (Z(m) - floor((m - 3) / 2))
    return numer, m


def owh_32(m: int) -> tuple[int, int]:
    numer = (m + 2) * Z(m - 1)
    return numer, (m - 2)


def vertex_average(n: int) -> tuple[int, int]:
    """Delete every vertex; endpoints leave K_{n-1}, other vertices leave K_{n-1}-e."""
    numer = 2 * Z(n - 1) + (n - 2) * target(n - 1)
    return numer, (n - 4)


def main() -> None:
    print("n target owh31_numer/denom ceil31 deficit*denom owh32_gap vertex_gap")
    for s in range(3, 16):
        n = 2 * s + 1
        T = target(n)
        a, da = owh_31(n)
        b, db = owh_32(n)
        c, dc = vertex_average(n)
        # deficit of Theorem 3.1 against the integer target, times the denominator
        deficit_times_den = T * da - a
        claim_times_den = (s - 1) * (s - 2) // 2  # since den = 2s+1 = n
        assert da == n
        assert deficit_times_den == claim_times_den
        ceil31 = -((-a) // da)  # ceil(a/da)
        gap32 = T * db - b
        gapV = T * dc - c
        print(
            f"{n} {T} {a}/{da} ceil={ceil31} "
            f"def={deficit_times_den}/{da} "
            f"32gap={gap32}/{db} Vgap={gapV}/{dc}"
        )
        if n <= 13:
            assert ceil31 == T
        else:
            assert ceil31 <= T - 1
            assert gap32 > 0 and gapV > 0
    for n in range(6, 40, 2):
        numer, den = owh_32(n)
        assert numer == target(n) * den
    print("ALL GAP CHECKS PASSED")


if __name__ == "__main__":
    main()
