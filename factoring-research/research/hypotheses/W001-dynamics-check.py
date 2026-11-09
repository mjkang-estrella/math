"""Finite algebra checks for W001; no factoring benchmark or hidden-factor solver.

Run from the project root with:
    timeout 60s python3 research/hypotheses/W001-dynamics-check.py
Writes no files. All enumerated moduli are public mathematical test parameters.
"""

from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import product
from math import gcd


def endpoint(x, shifts, modulus):
    for b in shifts:
        x = (x + b) ** 2 % modulus
    return x


def collision_count(modulus, depth):
    count = 0
    for shifts in product(range(modulus), repeat=depth):
        bins = Counter(endpoint(x, shifts, modulus) for x in range(modulus))
        count += sum(c * c for c in bins.values())
    return Fraction(count, modulus ** (depth + 2))


for prime in (3, 5, 7):
    for depth in range(4):
        observed = collision_count(prime, depth)
        predicted = 1 - Fraction(prime - 1, prime) ** (depth + 1)
        assert observed == predicted, (prime, depth, observed, predicted)
print("Shifted-square pair law: 12 exhaustive prime/depth cases passed.")

for p, q, depth in ((3, 5, 0), (3, 5, 1), (3, 5, 2), (5, 7, 1)):
    modulus = p * q
    good = 0
    total = modulus ** (depth + 2)
    for shifts in product(range(modulus), repeat=depth):
        values = [endpoint(x, shifts, modulus) for x in range(modulus)]
        for x in values:
            for y in values:
                good += 1 < gcd(x - y, modulus) < modulus
    cp = 1 - Fraction(p - 1, p) ** (depth + 1)
    cq = 1 - Fraction(q - 1, q) ** (depth + 1)
    assert Fraction(good, total) == cp * (1 - cq) + cq * (1 - cp)
print("CRT useful-pair law: 4 exhaustive semiprime/depth cases passed.")

for prime in (5, 7, 11, 17, 23, 43):
    for exponent in (2, 4, 6, 12, 60):
        bins = Counter(pow(x, exponent, prime) for x in range(1, prime))
        observed = Fraction(sum(c * c for c in bins.values()), (prime - 1) ** 2)
        assert observed == Fraction(gcd(exponent, prime - 1), prime - 1)
print("Power-image collision law: 30 exhaustive prime/exponent cases passed.")


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return tuple(a)


def mul(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return trim(result)


def sub(a, b):
    result = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        result[i] += x
    for i, x in enumerate(b):
        result[i] -= x
    return trim(result)


def power(a, k):
    result = (1,)
    for _ in range(k):
        result = mul(result, a)
    return result


@cache
def psi(k):
    # Division polynomials for E_a: y^2 = x^3 + a*x + 1 at P=(0,1).
    bases = {0: (0,), 1: (1,), 2: (2,), 3: (0, 0, -1), 4: (-32, 0, 0, -4)}
    if k in bases:
        return bases[k]
    m = k // 2
    if k % 2:
        return sub(mul(psi(m + 2), power(psi(m), 3)),
                   mul(psi(m - 1), power(psi(m + 1), 3)))
    result = mul(psi(m), sub(mul(psi(m + 2), power(psi(m - 1), 2)),
                            mul(psi(m - 2), power(psi(m + 1), 2))))
    assert all(x % 2 == 0 for x in result)
    return trim([x // 2 for x in result])


degrees = {}
for k in range(2, 34):
    degree = len(psi(k)) - 1
    predicted = (k * k - 1) // 4 if k % 2 else (k * k) // 4 - 1
    assert degree == predicted, (k, degree, predicted)
    degrees[k] = degree
print("Division-polynomial degrees: 32 exact integer-polynomial cases passed.")
print("Selected degrees:", {k: degrees[k] for k in (4, 8, 16, 32, 33)})
