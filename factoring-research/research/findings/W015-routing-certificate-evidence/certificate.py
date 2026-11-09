"""Fixed W015 algebra certificate, not an N-only factoring implementation."""
from __future__ import annotations

import json
from math import gcd, isqrt
from pathlib import Path

CASES = (25, 35, 77, 101, 143, 21311)
BUDGET = 20_000
visits = 0
checks = 0
failures: list[str] = []


def points(a: int, b: int):
    global visits
    for j in range(a + 1, b + 1):
        visits += 1
        if visits > BUDGET:
            raise RuntimeError("preregistered point-visit budget exceeded")
        yield j


def check(label: str, condition: bool):
    global checks
    checks += 1
    if not condition:
        failures.append(label)


def product(a: int, b: int, modulus: int) -> int:
    result = 1
    for j in points(a, b):
        result = result * j % modulus
    return result


def interval_product(intervals, modulus):
    result = 1
    for a, b in intervals:
        result = result * product(a, b, modulus) % modulus
    return result


def certificate(modulus: int):
    n = isqrt(modulus)
    prefix = n // 4
    depth = (n - 1).bit_length()
    target = product(0, n, modulus)
    stopped = [(0, prefix)]
    active = [(prefix, n)]
    alive = {x: x for x in points(prefix, n)}
    odd_witnesses = {x for x in points(prefix, n) if x % 2}
    exponent = 0
    rounds = []
    inv2 = pow(2, -1, modulus)
    for r in range(depth + 1):
        tag = f"N={modulus},round={r}"
        expanded = [j for a, b in active for j in points(a, b)]
        check(tag + ":disjoint", len(expanded) == len(set(expanded)))
        check(tag + ":pointwise", set(expanded) == set(alive.values()))
        check(tag + ":outside_prefix", all(prefix < x < modulus for x in expanded))
        check(tag + ":stopped_domain", all(0 <= a < b <= prefix for a, b in stopped))
        check(tag + ":odd_survival", odd_witnesses <= alive.keys())
        for original, value in alive.items():
            check(tag + f":gcd:{original}", gcd(original, modulus) == gcd(value, modulus))
        represented = (
            pow(2, exponent, modulus)
            * interval_product(stopped, modulus)
            * interval_product(active, modulus)
        ) % modulus
        check(tag + ":product", represented == target)
        rounds.append({
            "round": r, "active_records": len(active),
            "active_length": len(expanded), "stopped_records": len(stopped),
            "power_of_two_exponent": exponent, "product_residue": represented,
            "odd_survivors": len(odd_witnesses),
        })
        if r == depth:
            all_images = sorted(pow(inv2, depth, modulus) * x % modulus for x in points(0, n))
            check(tag + ":full_nonadjacency", all(b - a > 1 for a, b in zip(all_images, all_images[1:])))
            check(tag + ":singletons", all(b - a == 1 for a, b in active))
            check(tag + ":record_bound", len(active) >= (n - prefix) // 2)
            break
        new_active = []
        for a, b in active:
            children = [(a // 2, b // 2), ((a + modulus) // 2, (b + modulus) // 2)]
            check(tag + f":interval_identity:{a}:{b}",
                  product(a, b, modulus) == pow(2, b - a, modulus) * interval_product(children, modulus) % modulus)
            exponent += b - a
            for lo, hi in children:
                if lo < min(hi, prefix):
                    stopped.append((lo, min(hi, prefix)))
                if max(lo, prefix) < hi:
                    new_active.append((max(lo, prefix), hi))
        active = sorted(new_active)
        next_alive = {}
        for original, value in alive.items():
            # Independent formula: multiply by the inverse, not the parity split.
            global visits
            visits += 1
            if visits > BUDGET:
                raise RuntimeError("preregistered point-visit budget exceeded")
            updated = value * inv2 % modulus
            if updated > prefix:
                next_alive[original] = updated
        alive = next_alive
    return {"N": modulus, "n": n, "H": prefix, "s": depth, "rounds": rounds}


if __name__ == "__main__":
    results = []
    try:
        for modulus in CASES:
            results.append(certificate(modulus))
    except Exception as exc:
        failures.append(f"execution: {type(exc).__name__}: {exc}")
    output = {
        "scope": "Fixed exact routing identities and fragmentation fixtures; no timing or factoring bound",
        "scheduled_cases": list(CASES), "completed_cases": len(results),
        "point_visits": visits, "budget": BUDGET, "assertions": checks,
        "failures": failures, "cases": results,
    }
    path = Path(__file__).with_name("output.json")
    if path.exists():
        raise RuntimeError("refusing to replace retained certificate output")
    path.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: output[k] for k in ("completed_cases", "point_visits", "assertions", "failures")}))
    raise SystemExit(bool(failures) or len(results) != len(CASES))
