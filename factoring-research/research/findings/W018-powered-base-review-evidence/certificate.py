"""One fixed proof-only exhaustive certificate; not a solver or benchmark."""
import bisect
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import signal
import sys
import time

ROOT = Path(__file__).resolve().parent
LIMIT = 20000
SECONDS = 60
events = Counter()
checks = 0
failures = []
records = []
summaries = []
samplers = []
oracle_cache = {}
started = time.monotonic()


class BudgetStop(Exception):
    pass


def tick(kind):
    if sum(events.values()) >= LIMIT:
        raise BudgetStop("charged-event limit")
    if time.monotonic() - started >= SECONDS:
        raise BudgetStop("wall-time limit")
    events[kind] += 1


def check(ok, label, context):
    global checks
    checks += 1
    if not ok:
        failures.append({"check": label, "context": context})


def mulmod(x, y, n):
    tick("modular_multiply")
    return (x * y) % n


def gcd(x, n):
    tick("gcd")
    return math.gcd(x, n)


def rem(x, n):
    tick("integer_remainder")
    return x % n


def v2(x):
    tick("valuation")
    return (x & -x).bit_length() - 1


def power(a, exponent, n):
    # Scan the existing binary digits once; no fixture data in this function.
    x = 1
    for bit in bin(exponent)[2:]:
        x = mulmod(x, x, n)
        if bit == "1":
            x = mulmod(x, a, n)
    return x


def bounded_order(beta, n, bound):
    tick("integer_sqrt")
    b = math.isqrt(bound - 1) + 1
    babies = []
    x = 1
    for i in range(b):
        if i and x == 1:
            return i, {"branch": "duplicate_baby", "b": b, "matches": []}
        babies.append((x, i))
        x = mulmod(x, beta, n)
    babies.sort()
    # x is beta**b, including the b=1 branch.
    step = x
    giant = 1
    tick("integer_ceil_division")
    giant_count = (bound + b - 1) // b
    matches = []
    rejected = []
    for k in range(1, giant_count + 1):
        giant = mulmod(giant, step, n)
        tick("sorted_lookup")
        pos = bisect.bisect_left(babies, (giant, -1))
        if pos < len(babies) and babies[pos][0] == giant:
            tick("annihilator_index_arithmetic")
            r = k * b - babies[pos][1]
            if 1 <= r <= bound:
                matches.append(r)
            else:
                rejected.append(r)
    r = min(matches) if matches else None
    return r, {"branch": "giants", "b": b, "matches": matches,
               "rejected_matches": rejected}


def trial(n, exponent, bound, a):
    """Candidate boundary: N, M, B, a only; no orders/factors passed in."""
    g = gcd(a, n)
    if g > 1:
        return {"outcome": "factor_initial", "factor": g}
    beta = power(a, exponent, n)
    r, search = bounded_order(beta, n, bound)
    result = {"beta": beta, "order_result": r, "search": search}
    if r is None:
        result["outcome"] = "large_order"
        return result
    tick("annihilator_multiply")
    annihilator = exponent * r
    s = v2(annihilator)
    tick("odd_part_shift")
    odd = annihilator >> s
    x = power(a, odd, n)
    chain = []
    result.update({"E": annihilator, "s": s, "odd": odd, "chain": chain})
    for j in range(s + 1):
        if x == 1:
            chain.append({"j": j, "x": x, "gcd": n})
            break
        g = gcd(x - 1, n)
        chain.append({"j": j, "x": x, "gcd": g})
        if 1 < g < n:
            result.update({"outcome": "factor_chain", "factor": g})
            return result
        if j < s:
            x = mulmod(x, x, n)
    result["outcome"] = "retry"
    return result


def naive_powers(a, n):
    """Independent fixture-only reference, by consecutive multiplication."""
    key = (a, n)
    if key not in oracle_cache:
        powers = [1]
        x = 1
        for r in range(1, n + 1):
            x = mulmod(x, a, n)
            if x == 1:
                oracle_cache[key] = powers
                break
            powers.append(x)
        else:
            raise ValueError("fixture reference requested for a nonunit")
    return oracle_cache[key]


def run():
    cases = json.loads((ROOT / "cases.json").read_text())
    for n in sorted({case["N"] for case in cases}):
        k = (n - 2).bit_length()
        accepted = []
        rejected = 0
        for bits in range(1 << k):
            tick("sampler_bitstring")
            if bits < n - 1:
                accepted.append(bits + 1)
            else:
                rejected += 1
        check(accepted == list(range(1, n)), "sampler_bijection", {"N": n})
        check(len(accepted) * 2 > (1 << k), "sampler_accepts_more_than_half", {"N": n})
        samplers.append({"N": n, "bits_per_draw": k,
                         "accepted_count": len(accepted), "rejected_count": rejected})
    for case_id, case in enumerate(cases):
        n, exponent, bound = case["N"], case["M"], case["B"]
        components = case["components"]
        check(math.prod(components) == n, "fixture_components", case)
        counts = Counter()
        valuations_equal = 0
        pair_equal = 0
        units = 0
        small = 0
        failed = 0
        for a in range(1, n):
            tick("base_visit")
            result = trial(n, exponent, bound, a)
            context = {"case_id": case_id, "N": n, "M": exponent, "B": bound, "a": a}
            record = {**context, **result}
            counts[result["outcome"]] += 1
            unit = gcd(a, n) == 1
            if "factor" in result:
                d = result["factor"]
                check(1 < d < n and rem(n, d) == 0, "proper_factor", record)
            if not unit:
                check(result["outcome"] == "factor_initial", "nonunit_succeeds", record)
                records.append(record)
                continue
            units += 1
            powers = naive_powers(a, n)
            local_orders = [len(naive_powers(rem(a, q), q)) for q in components]
            vals = [v2(r) for r in local_orders]
            all_equal = len(set(vals)) == 1
            valuations_equal += all_equal
            if len(vals) >= 2:
                pair_equal += vals[0] == vals[1]
            beta = result["beta"]
            beta_order = len(naive_powers(beta, n))
            expected_beta = powers[rem(exponent, len(powers))]
            check(beta == expected_beta, "powered_base", record)
            check(beta_order == len(powers) // gcd(len(powers), exponent), "powered_order_identity", record)
            expected_result = beta_order if beta_order <= bound else None
            check(result["order_result"] == expected_result, "exact_bounded_order", record)
            record.update({"fixture_order": len(powers), "fixture_beta_order": beta_order,
                           "local_orders": local_orders, "local_v2": vals})
            if beta_order > bound:
                check(result["outcome"] == "large_order", "large_order_output", record)
            else:
                small += 1
                check(rem(result["E"], len(powers)) == 0, "E_annihilates_original_a", record)
                check(result["outcome"] == ("retry" if all_equal else "factor_chain"),
                      "extraction_exact_failure_condition", record)
                for step in result["chain"]:
                    tick("chain_exponent_index")
                    e = result["odd"] << step["j"]
                    check(step["x"] == powers[rem(e, len(powers))], "chain_value", {**context, **step})
                if result["outcome"] == "retry":
                    failed += 1
                    check(result["chain"][-1]["x"] == 1, "retry_chain_finishes_at_one", record)
            records.append(record)
        summary = {"case_id": case_id, **case, "M_bits": exponent.bit_length(),
                   "units": units, "small_order_units": small, "failed_units": failed,
                   "failed_unit_fraction": str(Fraction(failed, units)),
                   "failed_given_small_fraction": str(Fraction(failed, small)) if small else None,
                   "failed_all_bases_fraction": str(Fraction(failed, n - 1)),
                   "all_valuations_equal_units": valuations_equal, "counts": dict(counts)}
        if case["theorem_domain"]:
            check(2 * failed <= units, "failure_at_most_half_units", summary)
            check(failed <= pair_equal, "failure_subset_pair_equality", summary)
            ss = [v2(p - 1) for p in case["primes"][:2]]
            predicted_pair = Fraction(4 ** min(ss) + 2, 3 * 2 ** sum(ss))
            check(Fraction(pair_equal, units) == predicted_pair, "exact_pair_probability", summary)
            summary["pair_equality_fraction"] = str(predicted_pair)
        else:
            summary["probability_theorem_applied"] = False
            check(failed == units, "excluded_prime_power_control_all_units_retry", summary)
        summaries.append(summary)


status = "complete"
error = None


def timeout_handler(signum, frame):
    raise BudgetStop("signal wall-time limit")


signal.signal(signal.SIGALRM, timeout_handler)
signal.alarm(SECONDS)
try:
    run()
except Exception as exc:
    status = "incomplete"
    error = {"type": type(exc).__name__, "message": str(exc)}
    failures.append({"check": "run_completed", "context": error})
finally:
    signal.alarm(0)
    output = {"status": status, "error": error, "checks": checks, "failures": failures,
              "charged_events": sum(events.values()), "event_vector": dict(events),
              "elapsed_seconds_diagnostic_only": time.monotonic() - started,
              "limits": {"seconds": SECONDS, "charged_events": LIMIT},
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "cases_sha256": hashlib.sha256((ROOT / "cases.json").read_bytes()).hexdigest(),
              "samplers": samplers, "summaries": summaries, "records": records}
    print(json.dumps(output, indent=2))
sys.exit(0 if status == "complete" and not failures else 1)
