"""Exact, deterministic toy instances, limited to 40-bit composites.

Prime generation uses exact trial division. It is setup work, not solver work.
The corpus is public development data, never a secret evaluation set.
"""
import hashlib
from math import isqrt
from random import Random

FAMILIES = ("balanced", "close", "unbalanced", "square")


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def random_prime(bits: int, rng: Random) -> int:
    for _ in range(10_000):
        n = rng.randrange(1 << (bits - 1), 1 << bits) | 1
        if is_prime(n):
            return n
    raise RuntimeError("prime generation budget exhausted")


def make_case(bits: int, family: str, seed: int, index: int) -> dict:
    if not 12 <= bits <= 40 or family not in FAMILIES:
        raise ValueError("use a known family and 12 <= bits <= 40")
    key = f"factoring-corpus-v1:{seed}:{bits}:{family}:{index}"
    rng = Random(int.from_bytes(hashlib.sha256(key.encode()).digest(), "big"))
    for _ in range(10_000):
        p = random_prime((bits + 1) // 2, rng)
        if family == "balanced":
            q = random_prime(bits // 2, rng)
            if abs(p - q) < (1 << max(1, bits // 2 - 3)):
                continue
        elif family == "close":
            q = p + 2
            while not is_prime(q):
                q += 2
        elif family == "square":
            q = p
        else:
            p = rng.choice((3, 5, 7, 11))
            # Keep primality generation bounded even at the 40-bit cap.
            if bits > 28:
                raise ValueError("unbalanced corpus is limited to 28 bits")
            q = random_prime(bits - p.bit_length() + 1, rng)
        n = p * q
        if n.bit_length() == bits:
            return {"id": f"{family}-{bits}-{index}", "n": n, "bits": bits,
                    "family": family, "composite": True, "factors": sorted([p, q])}
    raise RuntimeError(f"corpus generation exhausted: {key}")


def generate(config: dict) -> list[dict]:
    result = [make_case(bits, family, config["corpus_seed"], index)
              for bits in config["bits"] for family in config["families"]
              for index in range(config["samples_per_family"])]
    if config.get("include_controls", True):
        for n in (0, 1, 2, 3, 4, 8, 27, 97, 561, 1105):
            result.append({"id": f"control-{n}", "n": n, "bits": n.bit_length(),
                           "family": "control", "composite": n >= 4 and not is_prime(n)})
    return result

