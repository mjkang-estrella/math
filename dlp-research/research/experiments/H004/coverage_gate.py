#!/usr/bin/env python3
"""Frozen P1 integer-coverage diagnostic; no EC operations or DLP solver.

Implementation-only checkpoint: syntax checks permitted; arithmetic runs await
separate mathematical preflight. Hit arrays are offline diagnostic data.
"""
import argparse
import hashlib
import json
import math
import time
from collections import Counter
from pathlib import Path

PRIMES = (31, 61, 127, 251, 509, 1021)
GRID = ((1, 2), (1, 1), (3, 2), (2, 1))
DELTAS = (1, -1)
EVENT_CATEGORIES = (
    "comparisons", "integer_adds", "integer_subs", "integer_muls", "integer_divmods",
    "integer_isqrts", "modular_adds", "modular_subs", "modular_muls", "modular_rems",
    "configuration_processing", "parameter_processing", "dictionary_reads", "dictionary_writes",
    "table_reads", "table_writes", "metric_passes", "reference_metric_passes",
    "coverage_array_initializations", "coverage_insertions", "list_counter_initializations",
    "emissions", "identity_processing", "pair_processing", "collision_equation_processing",
)


class BudgetStop(Exception):
    pass


class Budget:
    """Disjoint charged events; nested observational counts are not repriced."""
    def __init__(self, limit, seconds):
        self.limit, self.seconds = limit, seconds
        self.started = time.monotonic()
        self.events = Counter({name: 0 for name in EVENT_CATEGORIES})
        self.observations = Counter({"inverse_calls": 0, "inverse_euclidean_steps": 0})
        self.total = 0

    def tick(self, name):
        if time.monotonic() - self.started >= self.seconds:
            raise BudgetStop("global monotonic elapsed-time cap exhausted")
        if self.total >= self.limit:
            raise BudgetStop("global algorithm-event cap exhausted")
        self.events[name] += 1
        self.total += 1

    def observe(self, name):
        # Metadata breakdown: never added to total, not an additional cost unit.
        self.observations[name] += 1

    def eq(self, x, y):
        self.tick("comparisons")
        return x == y

    def lt(self, x, y):
        self.tick("comparisons")
        return x < y

    def iadd(self, x, y):
        self.tick("integer_adds")
        return x + y

    def isub(self, x, y):
        self.tick("integer_subs")
        return x - y

    def imul(self, x, y):
        self.tick("integer_muls")
        return x * y

    def divmod(self, x, y):
        self.tick("integer_divmods")
        return divmod(x, y)

    def isqrt(self, x):
        self.tick("integer_isqrts")
        return math.isqrt(x)

    def snapshot(self):
        return dict(self.events)

    def delta(self, before):
        return {k: self.events[k] - before.get(k, 0) for k in sorted(self.events)
                if self.events[k] != before.get(k, 0)}


class Modular:
    """Each modular op includes its reduction; internal rem is not repriced."""
    def __init__(self, q, budget):
        self.q, self.B = q, budget

    def add(self, x, y):
        self.B.tick("modular_adds")
        return (x + y) % self.q

    def sub(self, x, y):
        self.B.tick("modular_subs")
        return (x - y) % self.q

    def mul(self, x, y):
        self.B.tick("modular_muls")
        return (x * y) % self.q

    def rem(self, x):
        self.B.tick("modular_rems")
        return x % self.q

    def inv(self, x):
        self.B.observe("inverse_calls")
        if self.B.eq(x, 0):
            raise ArithmeticError("inverse of zero")
        old_r, r, old_t, t = self.q, x, 0, 1
        while not self.B.eq(r, 0):
            self.B.observe("inverse_euclidean_steps")
            quotient, remainder = self.B.divmod(old_r, r)
            old_r, r = r, remainder
            old_t, t = t, self.B.isub(old_t, self.B.imul(quotient, t))
        if not self.B.eq(old_r, 1):
            raise ArithmeticError("noninvertible denominator in declared prime modulus")
        return self.rem(old_t)


def prime(q, B):
    if B.lt(q, 2):
        return False
    d = 2
    while not B.lt(q, B.imul(d, d)):
        if B.eq(B.divmod(q, d)[1], 0):
            return False
        d = B.iadd(d, 1)
    return True


def ceil_sqrt(q, B):
    r = B.isqrt(q)
    return r if B.eq(B.imul(r, r), q) else B.iadd(r, 1)


def grid_M(q, num, den, B):
    numerator = B.imul(B.imul(num, num), q)
    denominator = B.imul(2, B.imul(den, den))
    m = B.isqrt(B.divmod(numerator, denominator)[0])
    return 1 if B.lt(m, 1) else m


def configurations(q, B):
    """Candidate, baseline2 grid, then baseline3 grid/RR/allocation, in order."""
    configurations, seen = [], {}

    def insert(kind, m, bs, ss, cycle, grid=None):
        B.tick("configuration_processing")
        signature = (tuple(bs), tuple(ss), tuple(cycle))
        B.tick("dictionary_reads")
        existing = seen.get(signature)
        parameters = {"M": m, "c_numerator": None, "c_denominator": None}
        if grid is not None:
            parameters["c_numerator"], parameters["c_denominator"] = grid
        if existing is not None:
            B.tick("table_writes")
            configurations[existing]["coincident_parameters"].append(parameters)
            return
        B.tick("dictionary_writes")
        seen[signature] = len(configurations)
        B.tick("table_writes")
        configurations.append({"id": kind + "_" + str(len(configurations)),
            "kind": kind, "M": m, "b": bs, "s": ss, "cycle": cycle,
            "coincident_parameters": [parameters]})

    m = B.isqrt(B.divmod(q, 2)[0])
    insert("candidate_P1", m, [0, 1, 2, 3],
           [1, m, B.isub(B.isub(0, m), 1), B.iadd(B.imul(2, m), 1)], [0, 1, 2, 3])
    grid = []
    for num, den in GRID:
        B.tick("parameter_processing")
        B.tick("table_writes")
        grid.append((num, den, grid_M(q, num, den, B)))
    for num, den, m in grid:
        B.tick("table_reads")
        insert("baseline2", m, [0, 1], [1, B.isub(0, m)], [0, 1], (num, den))
    for num, den, m in grid:
        B.tick("table_reads")
        for cycle in ([0, 1, 2], [0, 0, 1, 2]):
            insert("baseline3", m, [0, 1, 2], [1, m, B.isub(0, m)], cycle, (num, den))
    return configurations


def exact_metrics(result, q, cap, fallback, B):
    result["phase"] = "metric_pass"
    histogram = {}
    result["partial_hit_histogram"] = histogram
    failures, prefix_sum, metric_processed = 0, 0, 0
    for k in range(q):
        B.tick("metric_passes")
        B.tick("table_reads")
        hit = result["hit_time"][k]
        if B.eq(hit, None):
            term = cap
            failures = B.iadd(failures, 1)
            bucket = "uncovered_at_cap"
        else:
            term = hit if B.lt(hit, cap) else cap
            bucket = str(hit)
        prefix_sum = B.iadd(prefix_sum, term)
        B.tick("dictionary_reads")
        count = histogram.get(bucket, 0)
        value = B.iadd(count, 1)
        B.tick("dictionary_writes")
        histogram[bucket] = value
        metric_processed = B.iadd(metric_processed, 1)
        # Metadata persists exact progress if a later event hits the cap.
        result["partial_metric"] = {"processed": metric_processed,
            "prefix_sum": prefix_sum, "failures_in_processed_prefix": failures}
    fallback_sum = B.imul(failures, fallback)
    total_sum = B.iadd(prefix_sum, fallback_sum)
    result.update({"hit_histogram": histogram,
        "failures": failures, "failure_status": "none" if failures == 0 else "prefix_uncovered",
        "prefix_mean": {"numerator": prefix_sum, "denominator": q},
        "fallback_output_charge": fallback_sum,
        "prefix_plus_fallback_mean": {"numerator": total_sum, "denominator": q},
        "complete": True, "phase": "complete"})
    del result["partial_hit_histogram"]
    del result["partial_metric"]


def coverage(q, config, cap, fallback, result, B):
    F = Modular(q, B)
    result.update({"parameters": config, "q": q, "prefix_cap": cap,
        "complete": False, "phase": "array_initialization", "labels": [],
        "hit_time": [], "emissions": 0, "covered": 0,
        "zero_denominator_tautologies": 0, "zero_denominator_contradictions": 0,
        "scalar_equations": 0, "identity_equations": 0,
        "same_list_negation_equations": 0})
    for _ in range(q):
        B.tick("coverage_array_initializations")
        result["hit_time"].append(None)
    B.tick("coverage_insertions")
    result["hit_time"][0] = 0  # Direct input Q=O, before any emitted label.
    result["covered"] = 1
    bs, strides, cycle = config["b"], config["s"], config["cycle"]
    counters = []
    for _ in bs:
        B.tick("list_counter_initializations")
        counters.append(0)
    result["phase"] = "emissions"

    def insert(k, output_count):
        B.tick("coverage_insertions")
        B.tick("table_reads")
        old = result["hit_time"][k]
        if B.eq(old, None):
            B.tick("table_writes")
            result["hit_time"][k] = output_count
            result["covered"] = B.iadd(result["covered"], 1)
        return B.eq(result["covered"], q)

    for emission_index in range(cap):
        B.tick("emissions")
        slot = B.divmod(emission_index, len(cycle))[1]
        B.tick("table_reads")
        i = cycle[slot]
        B.tick("table_reads")
        j = counters[i]
        B.tick("table_reads")
        stride = strides[i]
        B.tick("table_reads")
        b = bs[i]
        a = F.mul(j, stride)
        following_j = B.iadd(j, 1)
        B.tick("table_writes")
        counters[i] = following_j
        output_count = B.iadd(emission_index, 1)
        result["emissions"] = output_count
        new = {"list": i, "j": j, "a": a, "b": b,
               "emission_index": emission_index, "output_count": output_count}
        prior_count = len(result["labels"])
        B.tick("table_writes")
        result["labels"].append(new)
        all_covered = False
        if not B.eq(b, 0):
            B.tick("identity_processing")
            result["identity_equations"] += 1  # Observation, not another charged operation.
            k = F.mul(F.sub(0, a), F.inv(b))
            all_covered = insert(k, output_count)
        if not all_covered:
            for prior_index in range(prior_count):
                B.tick("pair_processing")
                B.tick("table_reads")
                old = result["labels"][prior_index]
                for delta in DELTAS:
                    B.tick("collision_equation_processing")
                    d = F.sub(b, F.mul(delta, old["b"]))
                    numerator = F.sub(F.mul(delta, old["a"]), a)
                    if B.eq(d, 0):
                        key = ("zero_denominator_tautologies" if B.eq(numerator, 0)
                               else "zero_denominator_contradictions")
                        result[key] += 1
                        # No scalar is supplied even for the tautology 0=0.
                        continue
                    result["scalar_equations"] += 1
                    if B.eq(delta, -1) and B.eq(i, old["list"]):
                        result["same_list_negation_equations"] += 1
                    k = F.mul(numerator, F.inv(d))
                    all_covered = insert(k, output_count)
                    if all_covered:
                        break
                if all_covered:
                    break
        if all_covered:
            result["coverage_stop"] = "all_scalars_covered"
            break
    else:
        result["coverage_stop"] = "prefix_cap_reached"
    result["phase"] = "coverage_done"
    exact_metrics(result, q, cap, fallback, B)


def reference_minima(profile, B):
    """Grid minima are retrospective references, never adopted schedules."""
    references = {}
    for kind in ("baseline2", "baseline3"):
        record = {}
        for metric in ("prefix_mean", "prefix_plus_fallback_mean"):
            best, ids = None, []
            for result in profile["configs"]:
                B.tick("reference_metric_passes")
                if not B.eq(result["parameters"]["kind"], kind):
                    continue
                numerator = result[metric]["numerator"]
                if best is None or B.lt(numerator, best):
                    best, ids = numerator, [result["parameters"]["id"]]
                elif B.eq(numerator, best):
                    ids.append(result["parameters"]["id"])
            record[metric] = {"numerator": best, "denominator": profile["q"],
                              "minimizing_config_ids": ids}
        references[kind] = record
    profile["reference_grid_minima_only"] = references


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-events", type=int, default=1_000_000)
    parser.add_argument("--seconds", type=float, default=60.0)
    args = parser.parse_args()
    if not (0 < args.max_events <= 1_000_000 and 0 < args.seconds <= 60):
        parser.error("only positive caps no larger than 1M events and 60 seconds are allowed")
    B = Budget(args.max_events, args.seconds)
    output = {"protocol": "H004 P1 frozen coverage implementation v1",
        "diagnostic_only": True, "elliptic_operations": 0, "seeds": [],
        "primes": PRIMES, "baseline_c_grid": GRID, "deltas": DELTAS,
        "config_order": "candidate; baseline2 c-order; baseline3 c-order then RR/0012",
        "scalar_zero": "T(0)=0 by direct Q=O input test before outputs",
        "time_convention": "label at index e has output count e+1",
        "event_convention": "disjoint algorithm events; nested observations not priced again",
        "excluded_costs": ["integer bit complexity", "Python interpreter/control internals",
            "JSON/hash/I/O", "allocation/GC", "dictionary hashing internals",
            "metadata record operations", "PRNG (unused)", "elliptic curve arithmetic",
            "actual collision lookup", "physical memory traffic"],
        "hit_arrays": "offline diagnostic data, never advice available to a solver",
        "fallback": "fixed full signed2 output charge, not simulated arithmetic or early-stop cost",
        "verified_improvement": "NONE", "complete": False,
        "event_limit": B.limit, "seconds_limit": B.seconds, "profiles": []}
    active_before = None
    active_profile = None
    active_config = None
    try:
        for q in PRIMES:
            profile_before = B.snapshot()
            profile = {"q": q, "complete": False, "phase": "integer_setup", "configs": []}
            output["profiles"].append(profile)
            active_profile, active_config, active_before = profile, None, None
            if not prime(q, B):
                raise ArithmeticError("declared modulus is not prime")
            m = ceil_sqrt(q, B)
            cap = B.iadd(B.imul(2, m), 4)
            fallback = B.imul(2, B.iadd(m, 1))
            profile.update({"ceil_sqrt_q": m, "prefix_cap": cap,
                "fallback_description": {"b": [0, 1], "s": [1, B.isub(0, m)],
                    "indices_each_list": [0, m], "inclusive": True,
                    "full_output_count_F": fallback,
                    "charge_every_failed_scalar": True, "simulated": False}})
            configs = configurations(q, B)
            profile["declared_deduplicated_configs"] = configs
            profile["setup_event_vector"] = B.delta(profile_before)
            profile["phase"] = "coverage_configs"
            for config in configs:
                active_before = B.snapshot()
                result = {"complete": False, "parameters": config, "phase": "starting"}
                profile["configs"].append(result)
                active_config = result
                coverage(q, config, cap, fallback, result, B)
                result["event_vector"] = B.delta(active_before)
            profile["phase"] = "reference_minima"
            reference_minima(profile, B)
            profile.update({"complete": True, "phase": "complete",
                            "event_vector": B.delta(profile_before)})
        output.update({"complete": True, "status": "complete_diagnostic"})
    except BudgetStop as exc:
        output.update({"status": "incomplete_budget_stop", "stop_reason": str(exc)})
    except Exception as exc:
        output.update({"status": "incomplete_validation_failure",
                       "stop_reason": type(exc).__name__ + ": " + str(exc)})
    if active_config is not None and not active_config["complete"] and active_before is not None:
        active_config["partial_event_vector"] = B.delta(active_before)
    if active_profile is not None and not active_profile["complete"]:
        active_profile["incomplete_phase"] = active_profile["phase"]
    output.update({"charged_event_vector": dict(B.events), "total_events": B.total,
        "nested_observations_not_priced": dict(B.observations),
        "elapsed_seconds_before_output_finalization": time.monotonic() - B.started,
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "completed_profiles": sum(p["complete"] for p in output["profiles"]),
        "completed_configs": sum(c["complete"] for p in output["profiles"] for c in p["configs"])})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: output[k] for k in ("status", "total_events", "completed_profiles",
                                            "completed_configs", "verified_improvement")}))
    return 0 if output["complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
