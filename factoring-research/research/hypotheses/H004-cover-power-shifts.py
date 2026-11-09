#!/usr/bin/env python3
"""One preregistered finite diagnostic, never a candidate factoring solver."""
import bisect
import datetime
import hashlib
import json
import math
from pathlib import Path
import resource
import sys
import time

HERE = Path(__file__).resolve().parent
REPORT = HERE / "H004-prime-cover-construction.md"
PREFIX = "H004-cover-"
PRIMARY = [2, 3, 4, 5, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128]
REVISION = [2, 3, 4, 5, 6, 8, 12, 16, 24, 32]
START = time.monotonic()
DEADLINE = START + 50.0
COUNTS = {"modular_powers": 0, "direct_remainders": 0,
          "negative_product_multiplications": 0}


def checkpoint():
    if time.monotonic() > DEADLINE:
        raise TimeoutError("preregistered 50-second internal deadline")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save_json(name, obj):
    (HERE / (PREFIX + name)).write_text(json.dumps(obj, indent=2) + "\n")


def sieve(limit):
    mark = bytearray(b"\x01") * (limit + 1)
    mark[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        checkpoint()
        if mark[p]:
            mark[p*p:limit+1:p] = b"\x00" * ((limit-p*p)//p + 1)
    return [p for p, yes in enumerate(mark) if yes]


def cbrt_ceil(x):
    lo, hi = 0, 1
    while hi ** 3 < x:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** 3 >= x:
            hi = mid
        else:
            lo = mid
    return hi


def trial_prime(p):
    return p >= 2 and all(p % d for d in range(2, math.isqrt(p) + 1))


def case(m, e, primes, nominal):
    checkpoint()
    start = time.monotonic()
    R, L, B = m**3, m*m, 1 << e
    total = bisect.bisect_right(primes, R)
    automatic = bisect.bisect_right(primes, L)
    missed, residue_one, buckets = [], [], {}
    row_tests = 0
    for j in range(automatic, total):
        if (j - automatic) % 2048 == 0:
            checkpoint()
        p = primes[j]
        value = pow(2, e, p)
        COUNTS["modular_powers"] += 1
        row_tests += 1
        r = (-value) % p
        if 1 <= r <= L:
            if nominal:
                buckets.setdefault(r, []).append(p)
        else:
            missed.append(p)
            if value == 1:
                residue_one.append(p)
    result = {
        "m": m, "e": e, "R": R, "L": L,
        "set_size_each": m, "height": str(B + L + 1),
        "height_bits": (B + L + 1).bit_length(),
        "literal_B_bits": B.bit_length(), "exponent_bits": e.bit_length(),
        "m_bits": m.bit_length(), "prime_count": total,
        "automatic_covered_count": automatic, "covered_count": total-len(missed),
        "covered_above_L": total-automatic-len(missed),
        "missed_count": len(missed), "complete_cover": not missed,
        "smallest_miss": missed[0] if missed else None,
        "largest_misses": missed[-10:], "missed_primes": missed,
        "residue_one_misses": residue_one,
        "modular_power_tests": row_tests,
    }
    if nominal:
        if m <= 16:
            direct_misses = []
            for p in primes[:total]:
                found = False
                for i in range(1, L + 1):
                    COUNTS["direct_remainders"] += 1
                    if (B + i) % p == 0:
                        found = True
                        break
                if not found:
                    direct_misses.append(p)
            assert direct_misses == missed
            result["direct_enumeration_verified"] = True
        else:
            result["direct_enumeration_verified"] = None
        shell_misses = [p for p in missed if p > (m-1)**3]
        if len(shell_misses) >= 2:
            p, q = shell_misses[-2:]
            N = p*q
            assert trial_prime(p) and trial_prime(q) and p != q
            input_R = math.isqrt(N)
            assert cbrt_ceil(input_R) == m
            product = 1
            for i in range(1, L + 1):
                product = product * (B+i) % N
                COUNTS["negative_product_multiplications"] += 1
            g = math.gcd(N, product)
            assert g == 1
            result["negative_semiprime"] = {
                "p": p, "q": q, "N": N, "input_R": input_R,
                "rounded_m": m, "product_mod_N": product, "gcd": g,
                "prime_witnesses_checked_by_trial_division": True,
            }
        else:
            result["negative_semiprime"] = None
        result["leaf_collision"] = None
        for i in sorted(buckets):
            if len(buckets[i]) >= 2:
                p, q = buckets[i][:2]
                d = p*q
                assert (B+i) % d == 0 and d <= R*R
                result["leaf_collision"] = {
                    "i": i, "p": p, "q": q, "d": d,
                    "difference": str(B+i), "gcd_equals_d": math.gcd(d, B+i) == d,
                }
                break
    result["elapsed_seconds"] = time.monotonic()-start
    return result


def main():
    prereg = REPORT.read_bytes()
    script = Path(__file__).read_bytes()
    frozen = HERE / (PREFIX + "preregistration.md")
    if frozen.exists() or (HERE / (PREFIX + "results.json")).exists():
        raise RuntimeError("Existing evidence: refusing to overwrite or rerun")
    frozen.write_bytes(prereg)
    manifest = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "report_prereg_sha256": sha(prereg), "script_sha256": sha(script),
        "primary_m": PRIMARY, "revision_m": REVISION,
        "revision_e_rule": "all integers m <= e <= 4m, inclusive",
        "internal_cap_seconds": 50, "external_cap_seconds": 60,
        "python": sys.version, "no_randomness": True,
        "purpose": "finite prime-coverage diagnostic; construction charged",
    }
    save_json("manifest.json", manifest)
    results = {"nominal": [], "revision": [], "revision_best": [],
               "status": "running", "all_complete_cases": [], "unstarted": []}
    jobs = [("nominal", m, 2*m) for m in PRIMARY]
    jobs += [("revision", m, e) for m in REVISION for e in range(m, 4*m+1)]
    done = 0
    try:
        start_sieve = time.monotonic()
        primes = sieve(max(PRIMARY)**3)
        results["sieve"] = {"limit": max(PRIMARY)**3, "prime_count": len(primes),
                            "seconds": time.monotonic()-start_sieve}
        for kind, m, e in jobs:
            row = case(m, e, primes, kind == "nominal")
            results[kind].append(row)
            if row["complete_cover"]:
                results["all_complete_cases"].append({"kind": kind, "m": m, "e": e})
            done += 1
        results["status"] = "complete"
    except TimeoutError as exc:
        results["status"] = "censored"
        results["deadline_reason"] = str(exc)
    results["unstarted"] = [{"kind": k, "m": m, "e": e} for k, m, e in jobs[done:]]
    for m in REVISION:
        rows = [row for row in results["revision"] if row["m"] == m]
        if rows:
            best = min(rows, key=lambda row: (-row["covered_count"], row["e"]))
            results["revision_best"].append({
                key: best[key] for key in ["m", "e", "prime_count", "covered_count",
                                           "missed_count", "largest_misses", "complete_cover"]
            } | {"exponents_completed": len(rows), "exponents_planned": 3*m+1})
    results["counts"] = COUNTS
    results["peak_rss_kib_before_evidence_write"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    results["elapsed_before_evidence_write_seconds"] = time.monotonic()-START
    save_json("results.json", results)
    result_bytes = (HERE / (PREFIX + "results.json")).read_bytes()
    manifest.update({"result_sha256": sha(result_bytes), "status": results["status"],
                     "elapsed_including_result_write_seconds": time.monotonic()-START,
                     "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
    save_json("manifest.json", manifest)
    print(json.dumps({"status": results["status"], "jobs_completed": done,
                      "jobs_planned": len(jobs), "counts": COUNTS,
                      "elapsed_seconds": time.monotonic()-START,
                      "peak_rss_kib": manifest["peak_rss_kib"],
                      "all_complete_cases": results["all_complete_cases"]}, indent=2))


if __name__ == "__main__":
    main()
