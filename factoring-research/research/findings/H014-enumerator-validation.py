#!/usr/bin/env python3
"""One preregistered H014 validation; refuses to overwrite run evidence."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import resource
import signal
import sys
import time
import traceback
from fractions import Fraction

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PROTOCOL = HERE / "H014-enumerator-protocol.json"
RAW = HERE / "H014-enumerator-raw.jsonl"
RESULT = HERE / "H014-enumerator-results.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reference_resultant(f, a, b, c):
    """Independent Sylvester construction and rational Gaussian elimination."""
    d = len(f) - 1
    fd, gd = list(reversed(f)), [a, b, c]
    rows = []
    for shift in range(2):
        rows.append([Fraction(x) for x in
                     [0] * shift + fd + [0] * (1 - shift)])
    for shift in range(d):
        rows.append([Fraction(x) for x in
                     [0] * shift + gd + [0] * (d - 1 - shift)])
    det = Fraction(1)
    for j in range(d + 2):
        row = next((i for i in range(j, d + 2) if rows[i][j]), None)
        if row is None:
            return 0
        if row != j:
            rows[j], rows[row] = rows[row], rows[j]
            det = -det
        pivot = rows[j][j]
        det *= pivot
        for i in range(j + 1, d + 2):
            scale = rows[i][j] / pivot
            for k in range(j, d + 2):
                rows[i][k] -= scale * rows[j][k]
    assert det.denominator == 1
    return det.numerator


def reference_base(N, d):
    # Deliberately independent tiny-N base search, charged reference work.
    m = 1
    while (m + 1) ** d <= N:
        m += 1
    digits, q = [], N
    while q:
        digits.append(q % m)
        q //= m
    assert len(digits) == d + 1 and digits[-1] == 1
    return m, digits


def run_case(e, case):
    kind, stats = case["kind"], {}
    if kind == "cube":
        N, d, H = case["N"], case["d"], case["H"]
        setup_start = time.perf_counter()
        m, f = e.base_polynomial(N, d)
        threshold, c0 = e.threshold_for(N, f, H)
        if "threshold_override" in case:
            threshold = case["threshold_override"]
        start = time.perf_counter()
        emitted = list(e.enumerate_sublevel(f, H, threshold, stats))
        candidate_seconds = time.perf_counter() - start
        reference_start = time.perf_counter()
        assert (m, f) == reference_base(N, d)
        expected, cache, mismatches = [], {}, []
        count = 0
        for a, b, c in itertools.product(range(1, H + 1),
                                         range(-H, H + 1), range(-H, H + 1)):
            count += 1
            ref = reference_resultant(f, a, b, c)
            label = b + 2 * a, c - a
            if label not in cache:
                cache[label] = e.line_polynomial(f, *label)
            proposed = e.value(cache[label], a)
            if proposed != ref:
                mismatches.append({"g": [a, b, c], "proposed": proposed, "ref": ref})
            accepted = abs(ref) <= threshold
            if "threshold_override" not in case:
                assert accepted == (abs(ref) ** (5 * d) * N ** 6 <= c0 ** (5 * d))
            if accepted:
                expected.append((a, b, c))
        # Missing/extra triples and every coefficient mismatch are retained.
        missing = sorted(set(expected) - set(emitted))
        extra = sorted(set(emitted) - set(expected))
        unique = len(set(emitted)) == len(emitted)
        return {"pass": not missing and not extra and unique and not mismatches,
                "m": m, "f": f, "T": threshold, "C0": c0,
                "stats": stats, "fullcube_reference_triples": count,
                "emitted_count": len(emitted),
                "primitive_irreducible_count": sum(map(e.primitive_irreducible, emitted)),
                "emitted_sorted": sorted(emitted), "missing": missing, "extra": extra,
                "unique": unique, "resultant_mismatches": mismatches,
                "candidate_seconds": candidate_seconds,
                "reference_seconds": time.perf_counter() - reference_start,
                "total_with_setup_seconds": time.perf_counter() - setup_start}
    if kind == "sublevel":
        p, T, lo, hi = case["p"], case["T"], case["lo"], case["hi"]
        ranges = e.accepted_ranges(p, T, lo, hi, stats)
        actual = [x for a, b in ranges for x in range(a, b + 1)]
        # Independent elementary sum, no candidate polynomial evaluation.
        expected = [x for x in range(lo, hi + 1)
                    if abs(sum(c * x ** i for i, c in enumerate(p))) <= T]
        return {"pass": actual == expected, "actual": actual, "expected": expected,
                "ranges": ranges, "stats": stats}
    if kind == "wide":
        K = case["K"]
        ranges = e.accepted_ranges([K * K, -2 * K, 1], 0, 0, 2 * K, stats)
        return {"pass": ranges == [(K, K)] and stats["isolation_nodes"] <= 10000,
                "ranges": ranges, "expected": [[K, K]], "stats": stats}
    if kind == "integer_roots":
        failures, tests = [], 0
        for number, degree in itertools.product(case["numbers"], case["degrees"]):
            root = e.integer_root(number, degree)
            tests += 1
            if not root ** degree <= number < (root + 1) ** degree:
                failures.append([number, degree, root])
        return {"pass": not failures, "tests": tests, "failures": failures}
    if kind == "reject_nonmonic":
        try:
            e.base_polynomial(case["N"], case["d"])
        except ValueError as error:
            return {"pass": True, "expected_rejection": str(error)}
        return {"pass": False, "error": "accepted a nonmonic base polynomial"}
    raise ValueError(kind)


def main():
    start = time.perf_counter()
    if RAW.exists() or RESULT.exists():
        raise RuntimeError("registered evidence exists; no implicit rerun")
    protocol = json.loads(PROTOCOL.read_text())
    for filename, expected in protocol["source_hashes"].items():
        assert sha(HERE / filename) == expected, (filename, "source changed after preregistration")
    spec = importlib.util.spec_from_file_location("h014_candidate", HERE / "H014-enumerator-stdlib.py")
    e = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(e)

    def timeout(_signum, _frame):
        raise TimeoutError("preregistered 55-second attempt budget exhausted")

    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, max(0.001, 55 - (time.perf_counter() - start)))
    records, stopped = [], False
    with RAW.open("x") as raw:
        for case in protocol["cases"]:
            record = {"id": case["id"], "input": case}
            case_start = time.perf_counter()
            if stopped:
                record["status"] = "unstarted"
            else:
                try:
                    result = run_case(e, case)
                    record.update(result)
                    record["status"] = "pass" if result["pass"] else "failure"
                except TimeoutError as error:
                    record.update(status="timeout", error=str(error), counters="unknown")
                    stopped = True
                except Exception:
                    record.update(status="error", traceback=traceback.format_exc())
            record["seconds"] = time.perf_counter() - case_start
            records.append(record)
            raw.write(json.dumps(record, sort_keys=True) + "\n")
            raw.flush()
    signal.setitimer(signal.ITIMER_REAL, 0)
    summary = {"protocol_sha256": sha(PROTOCOL), "source_hashes": protocol["source_hashes"],
               "raw_sha256": sha(RAW), "cases": len(records),
               "status_counts": {s: sum(r["status"] == s for r in records)
                                 for s in ["pass", "failure", "error", "timeout", "unstarted"]},
               "seconds": time.perf_counter() - start,
               "process_peak_rss_kib_linux": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               "seed": None, "randomness": "none", "tracemalloc": False,
               "scope": "finite correctness only; no density or factoring claim"}
    with RESULT.open("x") as result:
        json.dump(summary, result, indent=2, sort_keys=True)
        result.write("\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
