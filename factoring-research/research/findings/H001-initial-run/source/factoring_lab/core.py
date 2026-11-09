from collections import Counter
from dataclasses import dataclass, field
from math import gcd, isqrt
from random import Random


def valid_factor(n: int, d: object) -> bool:
    # Reject bools, floats, trivial divisors, and malformed candidate output.
    return type(d) is int and 1 < d < n and n % d == 0


class BudgetExceeded(Exception):
    pass


@dataclass
class Meter:
    """Diagnostic event accounting, NOT a certified bit-machine cost model."""

    max_events: int = 20_000
    max_operand_bits: int = 4096
    events: Counter = field(default_factory=Counter)
    total: int = 0
    peak_operand_bits: int = 0
    width_squared_proxy: int = 0

    def tick(self, kind: str, *operands: int) -> None:
        width = max((abs(x).bit_length() for x in operands), default=1)
        if width > self.max_operand_bits:
            raise BudgetExceeded("operand width limit")
        if self.total >= self.max_events:
            raise BudgetExceeded("event limit")
        self.total += 1
        self.events[kind] += 1
        self.peak_operand_bits = max(self.peak_operand_bits, width)
        self.width_squared_proxy += max(1, width) ** 2

    def mod(self, a: int, b: int) -> int:
        self.tick("mod", a, b)
        return a % b

    def mul(self, a: int, b: int) -> int:
        self.tick("mul", a, b)
        result = a * b
        if result.bit_length() > self.max_operand_bits:
            raise BudgetExceeded("product width limit")
        return result

    def add(self, a: int, b: int) -> int:
        self.tick("add", a, b)
        return a + b

    def sub(self, a: int, b: int) -> int:
        self.tick("sub", a, b)
        return a - b

    def gcd(self, a: int, b: int) -> int:
        self.tick("gcd", a, b)
        return gcd(a, b)

    def sqrt(self, a: int) -> int:
        self.tick("isqrt", a)
        return isqrt(a)

    def randbelow(self, rng: Random, bound: int) -> int:
        self.tick("random_draw", bound)
        return rng.randrange(bound)

    def snapshot(self) -> dict:
        return {"events": dict(sorted(self.events.items())), "total_events": self.total,
                "peak_operand_bits": self.peak_operand_bits,
                "width_squared_proxy": self.width_squared_proxy}

