"""Small known baselines. Each receives ONLY n, its RNG, and a meter.

No factor oracle, corpus metadata, primality oracle, or free precomputation.
Loops/control flow and Python internals are not counted as arithmetic events.
"""
from random import Random

from .core import Meter


def trial(n: int, rng: Random, m: Meter) -> int | None:
    if n < 4:
        return None
    if m.mod(n, 2) == 0:
        return 2
    bound = m.sqrt(n)
    d = 3
    while d <= bound:
        if m.mod(n, d) == 0:
            return d
        d = m.add(d, 2)
    return None


def fermat(n: int, rng: Random, m: Meter) -> int | None:
    if n < 4:
        return None
    if m.mod(n, 2) == 0:
        return 2
    a = m.sqrt(n)
    if m.mul(a, a) < n:
        a = m.add(a, 1)
    while True:
        b2 = m.sub(m.mul(a, a), n)
        b = m.sqrt(b2)
        if m.mul(b, b) == b2:
            d = m.sub(a, b)
            return d if 1 < d < n else None
        a = m.add(a, 1)


def rho(n: int, rng: Random, m: Meter) -> int | None:
    """Floyd cycle detection; every failed walk/restart shares the same meter."""
    if n < 4:
        return None
    if m.mod(n, 2) == 0:
        return 2
    while True:
        m.tick("restart")
        x = m.add(2, m.randbelow(rng, n - 3))
        c = m.add(1, m.randbelow(rng, n - 1))
        y, d = x, 1

        def step(z: int) -> int:
            return m.mod(m.add(m.mul(z, z), c), n)

        while d == 1:
            x, y = step(x), step(step(y))
            d = m.gcd(abs(m.sub(x, y)), n)
        if d != n:
            return d


ALGORITHMS = {"trial": trial, "fermat": fermat, "rho": rho}

