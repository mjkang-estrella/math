"""Independent finite cross-check, not a proof or a performance benchmark.

Uses Python's modular inverse (not Lean's cubic inverse), enumerates coordinate
solutions without a supplied point list, and checks every scalar and triple.
Only the fixed synthetic curve over F5 is in scope. No external inputs.
"""
import json
from itertools import product

P, A, B = 5, 2, 1
G = (0, 1)


def add(left, right):
    if left is None:
        return right
    if right is None:
        return left
    x, y = left
    u, v = right
    if x == u and (y + v) % P == 0:
        return None
    if left == right:
        slope = (3 * x * x + A) * pow(2 * y, -1, P) % P
    else:
        slope = (v - y) * pow((u - x) % P, -1, P) % P
    xx = (slope * slope - x - u) % P
    return xx, (slope * (x - xx) - y) % P


def main():
    assert (4 * A**3 + 27 * B**2) % P != 0
    points = [None] + [
        (x, y) for x, y in product(range(P), repeat=2)
        if (y * y - x**3 - A * x - B) % P == 0
    ]
    for left, right in product(points, repeat=2):
        assert add(left, right) in points
        assert add(left, right) == add(right, left)
    for left, middle, right in product(points, repeat=3):
        assert add(add(left, middle), right) == add(left, add(middle, right))
    orbit = []
    current = None
    for _ in range(len(points)):
        assert current not in orbit
        orbit.append(current)
        current = add(current, G)
    assert current is None and set(orbit) == set(points)
    counts = []
    for secret, target in enumerate(orbit):
        current = None
        comparisons = 0
        for candidate in range(len(points)):
            comparisons += 1
            if current == target:
                assert candidate == secret
                break
            current = add(current, G)
        else:
            raise AssertionError("valid scalar missed")
        assert comparisons == secret + 1
        counts.append(comparisons)
    print(json.dumps({
        "curve": {"p": P, "a": A, "b": B, "generator": G},
        "points": points, "orbit": orbit,
        "closure_pairs": len(points)**2,
        "associativity_triples": len(points)**3,
        "all_scalar_comparisons": counts,
        "max_comparisons": max(counts),
        "sum_comparisons": sum(counts),
        "scope": "finite cross-check; no tape-step or timing claim",
    }, indent=2))


if __name__ == "__main__":
    main()
