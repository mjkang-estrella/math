"""Exact reference diagnostic for inverse-patch relaxations; not a fast IP solver."""
import hashlib
import json
import math
import platform
import random
import statistics
import time
from collections import Counter
from pathlib import Path

CONFIG = {"K": [10, 12, 14, 16], "seed": 1001, "samples": 8,
          "internal_seconds": 55, "reject_node_fraction": 0.8}


class Deadline(Exception):
    pass


def coefficients(n, k, s, a):
    modulus = 1 << k
    inv = pow(a, -1, modulus)
    return (n * inv % modulus, -n * inv * inv * (1 << s) % modulus,
            n * inv * inv * inv * (1 << (2 * s)) % modulus)


def relaxed(c, modulus, lo, hi, qlo, qhi, counts, deadline):
    """Solve the quadratic integer relaxation exactly by small reference loops."""
    c0, c1, c2 = c
    g = math.gcd(c2, modulus)
    period = modulus // g
    inv = pow(c2 // g, -1, period) if period > 1 else 0
    for t in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            raise Deadline
        lower = max(2 * lo * t - lo * lo, 2 * hi * t - hi * hi)
        upper = (lo + hi) * t - lo * hi
        for q in range(qlo, qhi + 1):
            counts["relaxation_pair_checks"] += 1
            rhs = q - c0 - c1 * t
            counts["peak_observed_integer_bits"] = max(
                counts["peak_observed_integer_bits"], abs(rhs).bit_length(),
                abs(lower).bit_length(), abs(upper).bit_length(), modulus.bit_length())
            if rhs % g:
                continue
            residue = ((rhs // g) * inv) % period if period > 1 else 0
            first = lower + ((residue - lower) % period)
            if first <= upper:
                return True
    return False


def probe(n, k, deadline):
    s = (k + 2) // 3
    modulus, step = 1 << k, 1 << s
    lower, upper = 1 << (k // 2 - 1), (1 << (k // 2)) - 1
    counts = Counter()
    rejects = Counter()
    found, truth_factors = set(), set()
    patch_count = 0
    full_nodes = 0
    start = time.monotonic()
    status = "complete"
    try:
        for a in range(1, step, 2):
            if time.monotonic() >= deadline:
                raise Deadline
            lo = max(0, (lower - a + step - 1) // step)
            hi = (upper - a) // step
            if lo > hi:
                continue
            patch_count += 1
            full_nodes += 2 * (hi - lo + 1) - 1
            c = coefficients(n, k, s, a)
            # Independent truth data is used only for assertion/reporting.
            exact = set()
            for t in range(lo, hi + 1):
                p = a + step * t
                q = n * pow(p, -1, modulus) % modulus
                assert (c[0] + c[1] * t + c[2] * t * t) % modulus == q
                counts["exact_truth_checks"] += 1
                if lower <= q <= upper:
                    assert p * q == n
                    exact.add(t)
                    truth_factors.add(p)
            stack = [(lo, hi, 0)]
            while stack:
                left, right, depth = stack.pop()
                counts["nodes"] += 1
                truth = any(left <= t <= right for t in exact)
                feasible = relaxed(c, modulus, left, right, lower, upper, counts, deadline)
                if not feasible:
                    assert not truth, ("unsound pruning", n, a, left, right)
                    rejects[depth] += 1
                    continue
                counts["feasible_nodes"] += 1
                if not truth:
                    counts["false_feasible_nodes"] += 1
                if left == right:
                    p = a + step * left
                    assert n % p == 0 and lower <= n // p <= upper
                    found.add(p)
                    continue
                mid = (left + right) // 2
                stack.extend(((mid + 1, right, depth + 1), (left, mid, depth + 1)))
    except Deadline:
        status = "partial"
    if status == "complete":
        assert found == truth_factors and found, (n, found, truth_factors)
    return {"n": n, "K": k, "s": s, "status": status, "counts": dict(counts),
            "patches_started": patch_count, "full_nodes_in_started_patches": full_nodes,
            "node_fraction": counts["nodes"] / full_nodes if status == "complete" else None,
            "rejection_depth_counts": dict(rejects), "found_factors": sorted(found),
            "truth_factors_in_started_patches": sorted(truth_factors),
            "seconds": time.monotonic() - start}


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def main():
    here = Path(__file__).resolve().parent
    output = here / "result.json"
    if output.exists():
        raise SystemExit("Refusing to overwrite existing evidence.")
    start = time.monotonic()
    deadline = start + CONFIG["internal_seconds"]
    c = coefficients(115, 8, 3, 1)
    assert c == (115, 104, 192)
    control_counts = Counter()
    assert relaxed(c, 256, 1, 3, 3, 5, control_counts, deadline)
    assert all(not 3 <= (c[0] + c[1] * t + c[2] * t * t) % 256 <= 5 for t in (1, 2, 3))
    rng = random.Random(CONFIG["seed"])
    rows, generations = [], []
    for k in CONFIG["K"]:
        lower, upper = 1 << (k // 2 - 1), (1 << (k // 2)) - 1
        primes = [p for p in range(lower, upper + 1) if is_prime(p)]
        pool = sorted({p * q for i, p in enumerate(primes) for q in primes[i + 1:]
                       if (p * q).bit_length() == k - 1})
        rng.shuffle(pool)
        selected = pool[:CONFIG["samples"]]
        generations.append({"K": k, "pool_size": len(pool), "selected_n": selected,
                            "requested_samples": CONFIG["samples"]})
        for n in selected:
            if time.monotonic() >= deadline:
                rows.append({"n": n, "K": k, "status": "unstarted"})
            else:
                rows.append(probe(n, k, deadline))
    summaries = []
    for k in CONFIG["K"]:
        group = [r for r in rows if r["K"] == k]
        done = [r for r in group if r["status"] == "complete"]
        summaries.append({"K": k, "status_counts": dict(Counter(r["status"] for r in group)),
                          "median_node_fraction": statistics.median(r["node_fraction"] for r in done) if done else None,
                          "total_false_feasible_nodes": sum(r["counts"].get("false_feasible_nodes", 0) for r in done),
                          "relaxation_pair_checks": sum(r["counts"].get("relaxation_pair_checks", 0) for r in done)})
    last = next((s for s in reversed(summaries) if s["median_node_fraction"] is not None), None)
    disposition = "inconclusive" if last is None else (
        "reject_cheap_relaxation" if last["median_node_fraction"] >= CONFIG["reject_node_fraction"]
        else "screen_pass_only_no_complexity_claim")
    protocol = here.parents[1] / "hypotheses/H005.md"
    result = {"schema": 1, "config": CONFIG, "python": platform.python_version(),
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "protocol_sha256": hashlib.sha256(protocol.read_bytes()).hexdigest(),
              "seconds": time.monotonic() - start, "false_feasible_control_verified": True,
              "generations": generations, "rows": rows, "summaries": summaries,
              "disposition": disposition, "limitation": "Exponential reference feasibility checks; no efficient IP or all-input tree bound."}
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"disposition": disposition, "summaries": summaries, "seconds": result["seconds"]}))


if __name__ == "__main__":
    main()
