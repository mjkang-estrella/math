#!/usr/bin/env python3
"""One frozen certificate, not a general factoring benchmark. Standard library only."""
import collections
import datetime
import hashlib
import json
from pathlib import Path
import platform
import signal
import sys
import time

ROOT = Path(__file__).resolve().parent


class Limit(Exception):
    pass


class Meter:
    def __init__(self, cap, deadline):
        self.cap = cap
        self.deadline = deadline
        self.counts = collections.Counter()
        self.total = 0
        self.max_operand_bits = 0

    def hit(self, name, count=1, operands=()):
        if self.total + count > self.cap:
            raise Limit("arithmetic_event_cap")
        if time.monotonic() >= self.deadline:
            raise Limit("wall_time_cap")
        self.counts[name] += count
        self.total += count
        for value in operands:
            self.max_operand_bits = max(self.max_operand_bits, abs(value).bit_length())


def difference(after, before):
    return {k: after[k] - before.get(k, 0) for k in sorted(after)
            if after[k] != before.get(k, 0)}


def parse_decimal(s, meter):
    n = 0
    for ch in s:
        meter.hit("input_decimal_digit", operands=(n,))
        n = 10 * n + (ord(ch) - ord("0"))
    meter.hit("input_validation", operands=(n,))
    if n < 3 or not (n & 1):
        raise ValueError("fixed certificate requires odd N >= 3")
    return n


def gcd(a, b, meter):
    meter.hit("gcd_call", operands=(a, b))
    while b:
        meter.hit("gcd_euclidean_remainder", operands=(a, b))
        a, b = b, a % b
    return a


def scalar_power(a, exponent, modulus, meter):
    result = 1
    while exponent:
        meter.hit("scalar_exponent_bit", operands=(exponent,))
        if exponent & 1:
            meter.hit("scalar_modmul", operands=(result, a))
            result = result * a % modulus
        exponent >>= 1
        if exponent:
            meter.hit("scalar_modmul", operands=(a, a))
            a = a * a % modulus
    return result


def convolution(a, b, n, r, meter):
    c = [0] * r
    # Dense work, including zero terms; no sparse/zero-skipping discount.
    for i in range(r):
        for j in range(r):
            index = (i + j) % r
            meter.hit("convolution_coefficient_mac", operands=(a[i], b[j], c[index], n))
            c[index] = (c[index] + a[i] * b[j]) % n
    return c


def polynomial_power(n, r, meter):
    meter.hit("polynomial_setup", count=2 * r + 2, operands=(n, r))
    result = [1] + [0] * (r - 1)
    base = [1, 1] + [0] * (r - 2)
    exponent = n
    products = 0
    while exponent:
        meter.hit("polynomial_exponent_bit", operands=(exponent,))
        if exponent & 1:
            result = convolution(result, base, n, r, meter)
            products += 1
        exponent >>= 1
        if exponent:
            base = convolution(base, base, n, r, meter)
            products += 1
    return result, products


def verified_factors(n, candidates, meter):
    witnesses = []
    for d in sorted(set(candidates)):
        if 1 < d < n:
            meter.hit("factor_verifier_call", operands=(n, d))
            meter.hit("factor_verifier_remainder", operands=(n, d))
            if n % d:
                raise AssertionError("invalid factor witness")
            witnesses.append({"factor": d, "proper": True, "remainder": 0})
    return witnesses


def independent_binomial_rows(n, rs, meter):
    # Integer recurrence, no cyclic powering and no hidden p,q.
    rows = {r: [0] * r for r in rs}
    coefficient = 1
    numerator = n
    for k in range(n + 1):
        if k:
            meter.hit("binomial_integer_multiply", operands=(coefficient, numerator))
            product = coefficient * numerator
            meter.hit("binomial_exact_divide", operands=(product, k))
            coefficient = product // k
            meter.hit("binomial_numerator_decrement", operands=(numerator,))
            numerator -= 1
        meter.hit("binomial_coefficient_remainder", operands=(coefficient, n))
        residue = coefficient % n
        for r in rs:
            meter.hit("binomial_fold_index", operands=(k, r))
            index = k % r
            meter.hit("binomial_fold_modadd", operands=(rows[r][index], residue, n))
            rows[r][index] = (rows[r][index] + residue) % n
    return rows


def timeout_handler(signum, frame):
    raise Limit("hard_wall_alarm")


def main():
    # Exclusive marker prevents an accidental rerun, including after failure.
    with (ROOT / "execution-started.json").open("x") as f:
        json.dump({"started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   "pid_note": "single execution, do not rerun"}, f)
    started = time.monotonic()
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, 60)
    protocol = json.loads((ROOT / "protocol.json").read_text())
    freeze = json.loads((ROOT / "certificate-freeze.json").read_text())
    for name, digest in freeze["sha256"].items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise RuntimeError("frozen payload mismatch: " + name)
    meter = Meter(protocol["event_cap"], started + protocol["seconds_cap"])
    rs = protocol["r_menu"]
    results = [{"N_decimal": s, "r": r, "status": "unstarted"}
               for s in protocol["N_decimal"] for r in rs]
    baselines = []
    audits = []
    stop = None
    active = None
    try:
        for s in protocol["N_decimal"]:
            before = dict(meter.counts)
            n = parse_decimal(s, meter)
            meter.hit("baseline_exponent_subtraction", operands=(n,))
            fermat_power = scalar_power(2, n - 1, n, meter)
            meter.hit("baseline_residue_subtraction", operands=(fermat_power,))
            fermat = gcd(fermat_power - 1, n, meter)
            base_witnesses = verified_factors(n, [fermat], meter)
            baselines.append({"N": n, "base2_power_Nminus1": fermat_power,
                              "base2_fermat_gcd": fermat, "verified_factors": base_witnesses,
                              "events": difference(meter.counts, before)})
            this_rows = []
            for r in rs:
                active = next(row for row in results if row["N_decimal"] == s and row["r"] == r)
                active["status"] = "started"
                before = dict(meter.counts)
                meter.hit("input_public_r", operands=(r,))
                sharing = gcd(n, r, meter)
                raw, products = polynomial_power(n, r, meter)
                corrected = raw.copy()
                meter.hit("correction_endpoint_index", operands=(n, r))
                for index in (0, n % r):
                    meter.hit("corrected_coefficient_modsubtract", operands=(corrected[index],))
                    corrected[index] = (corrected[index] - 1) % n
                raw_gcds = [gcd(value, n, meter) for value in raw]
                corrected_gcds = [gcd(value, n, meter) for value in corrected]
                witnesses = verified_factors(n, [sharing] + raw_gcds + corrected_gcds, meter)
                active.update(status="computed_pending_independent_audit", gcd_N_r=sharing,
                              r_class="sharing-factor-control" if sharing > 1 else "coprime-r",
                              raw_coefficients=raw, corrected_coefficients=corrected,
                              raw_gcd_vector=raw_gcds, corrected_gcd_vector=corrected_gcds,
                              polynomial_products=products,
                              verified_factors=witnesses, events=difference(meter.counts, before))
                this_rows.append(active)
                active = None
            before = dict(meter.counts)
            expected = independent_binomial_rows(n, rs, meter)
            errors = []
            for row in this_rows:
                r = row["r"]
                matches = expected[r] == row["raw_coefficients"]
                # Correction itself is the explicit two-endpoint identity above.
                row["independent_raw_coefficients_match"] = matches
                row["status"] = "verified" if matches else "failed_coefficient_audit"
                if not matches:
                    errors.append(r)
            audits.append({"N": n, "method": "exact_integer_binomial_recurrence_then_fold",
                           "expected_raw_coefficients": expected, "failed_r": errors,
                           "events": difference(meter.counts, before)})
    except Exception as e:
        stop = {"type": type(e).__name__, "message": str(e)}
        if active is not None:
            active["status"] = "failed_or_censored"
            active["error"] = stop
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        elapsed = time.monotonic() - started
        payload = {"protocol": protocol, "freeze": freeze, "python": sys.version,
                   "platform": platform.platform(), "elapsed_seconds": elapsed,
                   "events_total": meter.total, "event_vector": dict(sorted(meter.counts.items())),
                   "max_recorded_operand_bits": meter.max_operand_bits,
                   "stop": stop, "baselines": baselines, "cases": results,
                   "independent_audits": audits}
        with (ROOT / "certificate-result.json").open("x") as f:
            json.dump(payload, f, indent=2)
            f.write("\n")
        print(json.dumps({"events_total": meter.total, "elapsed_seconds": elapsed,
                          "statuses": dict(collections.Counter(row["status"] for row in results)),
                          "stop": stop}, indent=2))


if __name__ == "__main__":
    main()
