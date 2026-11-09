#!/usr/bin/env python3
"""Frozen W005 primitive evaluator. Standard library; not a solver/benchmark."""
import time

PROCESS_START = time.monotonic()
import collections
import hashlib
import json
import math
from pathlib import Path
import platform
import signal
import sys
import tracemalloc

CASES = ((49, 1), (49, 4), (77, 1), (77, 4), (91, 1), (91, 4),
         (121, 1), (121, 4))
BASE = Path(__file__).with_name("W005-blindnorm-review-evidence")
OUT = BASE / "screen"
MEMORY_CAP = 32 * 1024 * 1024
CASE_BYTES = 1024 * 1024
ALL_BYTES = 16 * 1024 * 1024
PAIR_CAP = 20000
WAVE_CAP = 60.0
# Reserve 40 ms of the one-second cap for recording a censored result.
WORK_CAP = 0.96


class StopCase(Exception):
    pass


def alarm_handler(signum, frame):
    raise StopCase("case_work_deadline")


def compact(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()


def counter_record(counter, modulus):
    entries = [[key // modulus, key % modulus, value]
               for key, value in sorted(counter.items())]
    return {"entries": entries, "sha256": hashlib.sha256(compact(entries)).hexdigest(),
            "support_size": len(counter), "total": sum(counter.values()),
            "multiplicity_histogram": dict(collections.Counter(counter.values()))}


def run_case(modulus, residue):
    started = time.monotonic()
    tracemalloc.reset_peak()
    state = {"N": modulus, "R": residue, "status": "UNKNOWN", "stop_reason": None,
             "processed_pairs": 0, "expected_pairs": modulus * modulus,
             "support_pairs_processed": 0, "affine_parameters_processed": 0,
             "unit_pairs": 0, "proper_factor_pairs": 0, "full_gcd_pairs": 0,
             "invalid_factors": 0, "invalid_certificates": 0}
    roots, full, affine = [], {}, {}
    proper = collections.Counter()
    affine_proper = collections.Counter()
    support = set()
    phi = None

    def checkpoint():
        if time.monotonic() - PROCESS_START >= WAVE_CAP - 0.05:
            raise StopCase("total_computation_budget")
        if time.monotonic() - started >= WORK_CAP:
            raise StopCase("case_work_deadline")
        if tracemalloc.get_traced_memory()[1] > MEMORY_CAP:
            raise StopCase("soft_traced_memory_cap")

    signal.setitimer(signal.ITIMER_REAL, WORK_CAP)
    try:
        checkpoint()
        roots = [x for x in range(modulus) if x * x % modulus == residue]
        phi = sum(math.gcd(x, modulus) == 1 for x in range(modulus))
        full = {x: collections.Counter() for x in roots}
        affine = {x: collections.Counter() for x in roots}
        for a in range(modulus):
            for b in range(modulus):
                if state["processed_pairs"] % 32 == 0:
                    checkpoint()
                if state["processed_pairs"] >= PAIR_CAP:
                    raise StopCase("pair_budget")
                h = (a * a + b * b) % modulus
                divisor = math.gcd(h, modulus)
                if divisor == 1:
                    inverse = pow(h, -1, modulus)
                    c = (a * a - b * b) * inverse % modulus
                    e = 2 * a * b * inverse % modulus
                    for x in roots:
                        u = x * (c - 2 * e) % modulus
                        v = x * (e + 2 * c) % modulus
                        full[x][u * modulus + v] += 1
                        if (u * u + v * v - 5 * residue) % modulus:
                            state["invalid_certificates"] += 1
                    state["unit_pairs"] += 1
                elif divisor == modulus:
                    state["full_gcd_pairs"] += 1
                else:
                    proper[divisor] += 1
                    state["proper_factor_pairs"] += 1
                    if not (1 < divisor < modulus and modulus % divisor == 0):
                        state["invalid_factors"] += 1
                # Increment only after the complete pair and all root outputs.
                state["processed_pairs"] += 1
        checkpoint()
        for u in range(modulus):
            for v in range(modulus):
                if state["support_pairs_processed"] % 64 == 0:
                    checkpoint()
                if (u * u + v * v - 5 * residue) % modulus == 0:
                    support.add(u * modulus + v)
                state["support_pairs_processed"] += 1
        affine_classes = collections.Counter()
        for b in range(modulus):
            checkpoint()
            h = (1 + b * b) % modulus
            divisor = math.gcd(h, modulus)
            if divisor == 1:
                affine_classes["unit"] += 1
                inverse = pow(h, -1, modulus)
                c = (1 - b * b) * inverse % modulus
                e = 2 * b * inverse % modulus
                for x in roots:
                    u, v = x * (c - 2 * e) % modulus, x * (e + 2 * c) % modulus
                    affine[x][u * modulus + v] += 1
            elif divisor == modulus:
                affine_classes["full_gcd"] += 1
            else:
                affine_classes["proper_factor"] += 1
                affine_proper[divisor] += 1
                if not (1 < divisor < modulus and modulus % divisor == 0):
                    state["invalid_factors"] += 1
            state["affine_parameters_processed"] += 1
        direct = {x: collections.Counter({x * modulus + (2 * x % modulus): 1})
                  for x in roots}
        first = roots[0]
        required = {
            "all_root_counters_identical": all(full[x] == full[first] for x in roots),
            "all_supports_exact": all(set(full[x]) == support for x in roots),
            "all_multiplicities_phi": all(all(v == phi for v in full[x].values())
                                           for x in roots),
            "all_proper_factors_valid": state["invalid_factors"] == 0,
            "all_certificates_valid": state["invalid_certificates"] == 0,
            "all_pairs_completed": state["processed_pairs"] == modulus * modulus,
            "direct_control_detects_dependence": len(roots) > 1 and
                not all(direct[x] == direct[first] for x in roots),
        }
        state["required_invariants"] = required
        state["direct_control"] = {str(x): counter_record(direct[x], modulus) for x in roots}
        state["affine_control"] = {
            "gcd_classes": dict(affine_classes), "proper_factor_counts": dict(affine_proper),
            "root_counters_identical": all(affine[x] == affine[first] for x in roots),
            "support_equals_full_norm_set": all(set(affine[x]) == support for x in roots),
            "conditional_distribution_equals_full": all(
                set(affine[x]) == set(full[x]) and all(
                    affine[x][key] * state["unit_pairs"] == full[x][key] * affine_classes["unit"]
                    for key in support) for x in roots),
        }
        state["norm_support"] = sorted(support)
        state["norm_support_encoding"] = "u*N+v"
        state["status"] = "PASS" if all(required.values()) else "REJECT"
        state["stop_reason"] = "completed" if all(required.values()) else "invariant_violation"
        checkpoint()
    except StopCase as exc:
        state["status"], state["stop_reason"] = "UNKNOWN", str(exc)
    except Exception as exc:
        state["status"], state["stop_reason"] = "UNKNOWN", "evaluator_error: " + repr(exc)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    state["work_seconds"] = time.monotonic() - started
    state["roots"], state["phi_by_exhaustive_gcd"] = roots, phi
    state["proper_factor_counts"] = dict(proper)
    state["full_counters"] = {str(x): counter_record(full[x], modulus) for x in full}
    state["affine_counters"] = {str(x): counter_record(affine[x], modulus) for x in affine}
    state["peak_traced_bytes"] = tracemalloc.get_traced_memory()[1]
    state["case_seconds_including_serialization"] = time.monotonic() - started
    payload = compact(state) + b"\n"
    if len(payload) > CASE_BYTES:
        state = {"N": modulus, "R": residue, "status": "UNKNOWN", "stop_reason": "case_evidence_cap",
                 "processed_pairs": state["processed_pairs"], "expected_pairs": modulus * modulus}
    if time.monotonic() - started >= 1.0:
        state["status"], state["stop_reason"] = "UNKNOWN", "case_deadline_including_evidence"
    if tracemalloc.get_traced_memory()[1] > MEMORY_CAP:
        state["status"], state["stop_reason"] = "UNKNOWN", "soft_traced_memory_cap"
    state["case_seconds_including_serialization"] = time.monotonic() - started
    state["peak_traced_bytes"] = tracemalloc.get_traced_memory()[1]
    return state


def main():
    if OUT.exists():
        raise SystemExit("Refusing to rerun or overwrite existing screen")
    OUT.mkdir()
    tracemalloc.start()
    signal.signal(signal.SIGALRM, alarm_handler)
    total_bytes = 0
    records = []
    for modulus, residue in CASES:
        # Check budgets before every case; retain unstarted cases in denominator.
        if time.monotonic() - PROCESS_START >= WAVE_CAP - 1.05:
            result = {"N": modulus, "R": residue, "status": "UNKNOWN", "stop_reason": "unstarted_total_budget",
                      "processed_pairs": 0, "expected_pairs": modulus * modulus}
        elif tracemalloc.get_traced_memory()[1] > MEMORY_CAP:
            result = {"N": modulus, "R": residue, "status": "UNKNOWN", "stop_reason": "unstarted_memory_cap",
                      "processed_pairs": 0, "expected_pairs": modulus * modulus}
        else:
            result = run_case(modulus, residue)
        payload = compact(result) + b"\n"
        if total_bytes + len(payload) > ALL_BYTES - 65536:
            result = {"N": modulus, "R": residue, "status": "UNKNOWN", "stop_reason": "overall_evidence_cap",
                      "processed_pairs": result["processed_pairs"], "expected_pairs": modulus * modulus}
            payload = compact(result) + b"\n"
        target = OUT / f"N{modulus}-R{residue}.json"
        target.write_bytes(payload)
        total_bytes += len(payload)
        records.append({key: result.get(key) for key in (
            "N", "R", "status", "stop_reason", "processed_pairs", "expected_pairs",
            "unit_pairs", "proper_factor_pairs", "full_gcd_pairs", "work_seconds",
            "case_seconds_including_serialization", "peak_traced_bytes")})
        records[-1].update({"file": target.name, "bytes": len(payload),
                            "sha256": hashlib.sha256(payload).hexdigest()})
        print(json.dumps(records[-1]), flush=True)
    summary = {"cases": records, "python": sys.version, "platform": platform.platform(),
               "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               "no_reruns": True, "seeds": None, "total_seconds": time.monotonic() - PROCESS_START,
               "case_evidence_bytes": total_bytes,
               "outcomes": dict(collections.Counter(r["status"] for r in records))}
    (OUT / "summary.json").write_bytes(compact(summary) + b"\n")
    print(json.dumps({"outcomes": summary["outcomes"], "total_seconds": summary["total_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
