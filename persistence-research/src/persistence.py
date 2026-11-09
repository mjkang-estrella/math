"""Core library for the multiplicative-persistence research project. READ-ONLY for subagents.

Definitions (base 10):
  Pi(n)  := product of the decimal digits of n            (Pi(0) = 0)
  P(n)   := persistence = number of applications of Pi needed to reach a
            single digit; P(n) = 0 for n < 10; P(n) = 1 + P(Pi(n)) for n >= 10.

Facts used (proofs in notes/theory.md):
  F1. P(n) = 1 + P(Pi(n)) for n >= 10.
  F2. If str(n) contains '0' and n >= 10, then Pi(n) = 0 and P(n) = 1. (exact)
  F3. Pi(n) < n for all n >= 10, so every chain terminates.
  F4. Pi(n) is 7-smooth: Pi(n) = 2^a * 3^b * 5^c * 7^d for some a,b,c,d >= 0.
  F5. max{P(n) : n < 10^7} = 8, attained first at n = 2677889
      (brute-force verified in src/test_core.py). Hence P(x) <= 8 for 10 <= x < 10^7.
"""
from math import prod

# ---------------------------------------------------------------------------
# basic maps
# ---------------------------------------------------------------------------

def digit_product(n: int) -> int:
    """Pi(n): product of decimal digits. Valid for all n >= 0."""
    return prod(map(int, str(n)))


def persistence(n: int) -> int:
    """Exact P(n). Uses only provably-equivalent shortcuts (see F2)."""
    steps = 0
    while n >= 10:
        s = str(n)
        if "0" in s:
            return steps + 1          # n -> 0, and 0 is a single digit
        n = prod(map(int, s))
        steps += 1
    return steps


def persistence_naive(n: int) -> int:
    """Reference implementation: no shortcuts at all. For validation."""
    steps = 0
    while n >= 10:
        n = digit_product(n)
        steps += 1
    return steps


def chain(n: int) -> list[int]:
    """Full orbit [n, Pi(n), Pi^2(n), ...] down to a single digit."""
    out = [n]
    while n >= 10:
        n = digit_product(n)
        out.append(n)
    return out


# ---------------------------------------------------------------------------
# 7-smooth helpers
# ---------------------------------------------------------------------------

def is_7smooth(n: int) -> bool:
    """n >= 1 has no prime factor above 7."""
    if n < 1:
        return False
    for p in (2, 3, 5, 7):
        while n % p == 0:
            n //= p
    return n == 1


def smooth(a: int, b: int, c: int, d: int) -> int:
    """2^a * 3^b * 5^c * 7^d."""
    return 2 ** a * 3 ** b * 5 ** c * 7 ** d


def prime_digit_expansion(a: int, b: int, c: int, d: int) -> int:
    """The integer whose decimal digits are a '2's, b '3's, c '5's, d '7's.

    digit_product(prime_digit_expansion(a,b,c,d)) == smooth(a,b,c,d).
    """
    s = "2" * a + "3" * b + "5" * c + "7" * d
    return int(s) if s else 1   # empty product is 1, whose digit product is 1


def len23_table(max_a: int, max_b: int) -> list[list[int]]:
    """len23[a][b] = min #digits from {2,3,4,6,8,9} whose product is 2^a*3^b.

    DP over the exponent vectors of those digits:
      2->(1,0) 3->(0,1) 4->(2,0) 6->(1,1) 8->(3,0) 9->(0,2).
    Optimal substructure: any optimal multiset, minus one digit, is optimal for
    the reduced exponent pair. Entry (0,0)=0. INF (10**9) marks unreachable,
    which cannot happen for a,b <= max within table bounds.
    """
    INF = 10 ** 9
    t = [[INF] * (max_b + 1) for _ in range(max_a + 1)]
    t[0][0] = 0
    for a in range(max_a + 1):
        for b in range(max_b + 1):
            if a == 0 and b == 0:
                continue
            best = INF
            if a >= 1 and t[a - 1][b] + 1 < best:
                best = t[a - 1][b] + 1          # digit 2
            if a >= 2 and t[a - 2][b] + 1 < best:
                best = t[a - 2][b] + 1          # digit 4
            if a >= 3 and t[a - 3][b] + 1 < best:
                best = t[a - 3][b] + 1          # digit 8
            if b >= 1 and t[a][b - 1] + 1 < best:
                best = t[a][b - 1] + 1          # digit 3
            if b >= 2 and t[a][b - 2] + 1 < best:
                best = t[a][b - 2] + 1          # digit 9
            if a >= 1 and b >= 1 and t[a - 1][b - 1] + 1 < best:
                best = t[a - 1][b - 1] + 1      # digit 6
            t[a][b] = best
    return t


def len_of_smooth(a: int, b: int, c: int, d: int, t23=None) -> int:
    """len(2^a*3^b*5^c*7^d): min #digits (1-9) whose product equals m.

    Exactly c + d + len23(a,b): each digit contributes at most one factor 5
    (only digit 5) and at most one factor 7 (only digit 7), and digits {5,7}
    contribute no 2s or 3s, so the three parts are independent.
    (Bug C-1 from the red team fixed: a=0 or b=0 no longer TypeError.)
    """
    if a == 0 and b == 0:
        return c + d
    if t23 is None:
        t23 = len23_table(a, b)
    return c + d + t23[a][b]
