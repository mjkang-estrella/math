"""Exact cardinality gate for an explicit CRT factor-sum sieve; not a new factorer."""
import hashlib
import json
import math
import platform
import time
from pathlib import Path


def primes(count):
    result = []
    x = 3
    while len(result) < count:
        if all(x % p for p in range(2, math.isqrt(x) + 1)):
            result.append(x)
        x += 2
    return result


def allowed(n, ell):
    assert n % ell
    squares = {x * x % ell for x in range(ell)}
    return [s for s in range(ell) if (s * s - 4 * n) % ell in squares]


def legendre(n, ell):
    value = pow(n % ell, (ell - 1) // 2, ell)
    assert value in (1, ell - 1)
    return 1 if value == 1 else -1


def main():
    output = Path(__file__).with_name("result.json")
    if output.exists():
        raise SystemExit("Refusing to overwrite existing evidence; select a new path explicitly.")
    start = time.perf_counter()
    all_primes = primes(64)
    local_checks = 0
    for ell in all_primes:
        if ell > 43:
            break
        for n in range(1, ell):
            assert 2 * len(allowed(n, ell)) == ell + legendre(n, ell)
            local_checks += 1
    explicit = []
    for n in (10403, 1022117):
        residues, modulus, product_count, cumulative_merges = [0], 1, 1, 0
        for k, ell in enumerate(all_primes[:6], 1):
            local = allowed(n, ell)
            inv = pow(modulus, -1, ell)
            next_residues = [r + modulus * ((s - r) * inv % ell)
                             for r in residues for s in local]
            cumulative_merges += len(next_residues)
            modulus *= ell
            product_count *= len(local)
            assert len(next_residues) == len(set(next_residues)) == product_count
            assert all(0 <= r < modulus for r in next_residues)
            direct_equal = None
            if k <= 5:
                local_sets = [(p, set(allowed(n, p))) for p in all_primes[:k]]
                direct = {s for s in range(modulus)
                          if all(s % p in good for p, good in local_sets)}
                direct_equal = direct == set(next_residues)
                assert direct_equal
            explicit.append({"n": n, "k": k, "modulus": modulus,
                             "local_size": len(local), "global_size": product_count,
                             "cumulative_crt_pair_merges": cumulative_merges,
                             "direct_filter_matches": direct_equal})
            residues = next_residues
    bounds = []
    modulus, lower, upper = 1, 1, 1
    for k, ell in enumerate(all_primes, 1):
        modulus *= ell
        lower *= (ell - 1) // 2
        upper *= (ell + 1) // 2
        assert lower * 3**k >= modulus
        assert 2 * modulus >= math.factorial(k + 2)
        if k in (1, 2, 4, 8, 16, 32, 64):
            bounds.append({"k": k, "largest_prime": ell, "modulus": modulus,
                           "modulus_bits": modulus.bit_length(),
                           "min_global_cardinality": lower, "max_global_cardinality": upper,
                           "log2_min_cardinality": math.log2(lower),
                           "log_cardinality_over_log_modulus": math.log(lower) / math.log(modulus),
                           "count_only_not_materialized": True})
    result = {"schema": 1, "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "python": platform.python_version(), "seconds": time.perf_counter() - start,
              "local_identities_checked": local_checks, "explicit_crt": explicit,
              "counts_only_bounds": bounds,
              "claim": "Known local sieve; explicit-set cardinality gate only. No new factoring bound."}
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"local_identities_checked": local_checks, "explicit_rows": len(explicit),
                      "seconds": result["seconds"], "output": str(output)}))


if __name__ == "__main__":
    main()
