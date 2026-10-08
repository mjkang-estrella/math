#!/usr/bin/env python3
"""Predeclared EDS correlation diagnostic, NOT a discrete-log solver.

Only syntax-checked before independent pre-run review. See eds_protocol.md.
The event vector is an explicit arithmetic/cache/access ledger, not CPU cycles.
"""
import argparse
import hashlib
import json
import random
import time
from collections import Counter
from pathlib import Path

SEEDS = (7, 19, 43)
FAMILY = ((0,), (0, 1), (0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 1, 2, 4, 8))
FIXTURES = (
    {"name": "normalization_plus", "p": 13, "a": 2, "b": 4,
     "q": 17, "P": (0, 2), "expected_c": 1},
    {"name": "normalization_minus", "p": 19, "a": 2, "b": 9,
     "q": 23, "P": (0, 16), "expected_c": -1},
)
SYNTHETIC = (
    {"name": "H001_59", "p": 59, "a": 28, "b": 27, "q": 73},
    {"name": "H001_127", "p": 127, "a": 78, "b": 87, "q": 139},
    {"name": "H001_251", "p": 251, "a": 218, "b": 156, "q": 257},
)


class BudgetStop(Exception):
    pass


class Ledger:
    def __init__(self, events, seconds):
        self.limit, self.seconds = events, seconds
        self.started = time.monotonic()
        self.counts = Counter()
        self.total = 0

    def tick(self, category, number=1):
        if time.monotonic() - self.started >= self.seconds:
            raise BudgetStop("monotonic elapsed-time budget exhausted")
        if self.total + number > self.limit:
            raise BudgetStop("global instrumented-event budget exhausted")
        self.counts[category] += number
        self.total += number

    def equal(self, x, y):
        self.tick("comparisons")
        return x == y

    def require(self, condition, message):
        self.tick("comparisons")
        if not condition:
            raise ArithmeticError(message)

    def snapshot(self):
        return dict(self.counts)

    def delta(self, before):
        return {k: self.counts[k] - before.get(k, 0) for k in sorted(self.counts)
                if self.counts[k] != before.get(k, 0)}

    def read(self, table, key):
        self.tick("table_reads")
        return table[key]


class Field:
    def __init__(self, p, ledger):
        self.p, self.ledger = p, ledger

    def add(self, x, y):
        self.ledger.tick("field_adds")
        return (x + y) % self.p

    def sub(self, x, y):
        self.ledger.tick("field_subs")
        return (x - y) % self.p

    def mul(self, x, y):
        self.ledger.tick("field_muls")
        return (x * y) % self.p

    def square(self, x):
        return self.mul(x, x)

    def cube(self, x):
        return self.mul(self.square(x), x)

    def pow(self, x, exponent):
        self.ledger.require(exponent >= 0, "negative field exponent")
        result = 1
        while exponent:
            self.ledger.tick("exponent_bits")
            if exponent & 1:
                self.ledger.tick("exponent_muls")
                result = self.mul(result, x)
            exponent >>= 1
            if exponent:
                self.ledger.tick("exponent_muls")
                x = self.square(x)
        return result

    def inv(self, x):
        self.ledger.tick("field_inversions")
        self.ledger.require(x != 0, "field inversion of zero")
        return self.pow(x, self.p - 2)

    def character(self, x):
        self.ledger.tick("characters")
        if self.ledger.equal(x, 0):
            return 0
        v = self.pow(x, (self.p - 1) // 2)
        if self.ledger.equal(v, 1):
            return 1
        self.ledger.require(v == self.p - 1, "non-prime field character result")
        return -1


def is_prime(n, ledger):
    ledger.tick("comparisons")
    if n < 2:
        return False
    d = 2
    while True:
        ledger.tick("integer_muls")
        ledger.tick("comparisons")
        if d * d > n:
            return True
        ledger.tick("integer_divmods")
        if ledger.equal(n % d, 0):
            return False
        d += 1
        ledger.tick("integer_adds")


def inverse_integer(a, modulus, ledger):
    """Counted extended Euclid; modulus p-1 is not a prime-field modulus."""
    old_r, r, old_t, t = modulus, a, 0, 1
    while r:
        ledger.tick("integer_divmods")
        quotient, remainder = divmod(old_r, r)
        old_r, r = r, remainder
        ledger.tick("integer_muls")
        ledger.tick("integer_subs")
        old_t, t = t, old_t - quotient * t
    ledger.require(old_r == 1, "q squared not invertible modulo p-1")
    ledger.tick("integer_divmods")
    return old_t % modulus


def sign_power(c, n, ledger):
    ledger.require(c in (-1, 1) and n >= 0, "invalid character power")
    ledger.tick("integer_divmods")
    return -1 if c == -1 and n % 2 else 1


def char_product(x, y, ledger):
    ledger.tick("character_muls")
    return x * y


class Curve:
    def __init__(self, spec, ledger):
        self.spec, self.ledger = spec, ledger
        self.p, self.a, self.b, self.q = (spec[k] for k in ("p", "a", "b", "q"))
        self.f = Field(self.p, ledger)

    def add(self, P, Q):
        self.ledger.tick("group_additions")
        if self.ledger.equal(P, None):
            return Q
        if self.ledger.equal(Q, None):
            return P
        x, y = P
        u, v = Q
        f = self.f
        if self.ledger.equal(x, u):
            if self.ledger.equal(f.add(y, v), 0):
                return None
            self.ledger.require(y == v, "same x with inconsistent y")
            numerator, denominator = f.add(f.mul(3, f.square(x)), self.a), f.mul(2, y)
        else:
            numerator, denominator = f.sub(v, y), f.sub(u, x)
        slope = f.mul(numerator, f.inv(denominator))
        xx = f.sub(f.sub(f.square(slope), x), u)
        yy = f.sub(f.mul(slope, f.sub(x, xx)), y)
        return xx, yy

    def scalar(self, P, n):
        self.ledger.tick("scalar_multiplications")
        self.ledger.require(n >= 0, "negative diagnostic scalar")
        result = None
        while n:
            self.ledger.tick("scalar_bits")
            if n & 1:
                result = self.add(result, P)
            n >>= 1
            if n:
                P = self.add(P, P)
        return result

    def validate(self):
        """Enumerate all affine points without uncharged square-root calls."""
        L, f = self.ledger, self.f
        L.require(self.p > 3 and is_prime(self.p, L), "invalid field prime")
        L.require(self.q > 3 and is_prime(self.q, L), "invalid group prime")
        L.require(self.q != self.p, "anomalous curve excluded")
        discriminant = f.add(f.mul(4, f.cube(self.a)), f.mul(27, f.square(self.b)))
        L.require(discriminant != 0, "singular curve")
        inverse_integer(self.q, self.p - 1, L)  # Explicit gcd(q,p-1)=1 admission.
        square_roots = {}
        for y in range(self.p):
            L.tick("loop_iterations")
            yy = f.square(y)
            L.tick("dictionary_reads")
            roots = square_roots.get(yy)
            if roots is None:
                roots = []
                L.tick("dictionary_writes")
                square_roots[yy] = roots
            L.tick("table_writes")
            roots.append(y)
        points = []
        for x in range(self.p):
            L.tick("loop_iterations")
            rhs = f.add(f.add(f.cube(x), f.mul(self.a, x)), self.b)
            L.tick("dictionary_reads")
            for y in square_roots.get(rhs, ()):
                L.tick("loop_iterations")
                L.tick("table_writes")
                points.append((x, y))
        L.require(len(points) + 1 == self.q, "declared full group order is wrong")
        return points


class DivisionPolynomial:
    """Pointwise psi_n. Memoized half-index recursion; no linear scan to n."""
    def __init__(self, curve, P):
        self.curve, self.L, self.f = curve, curve.ledger, curve.f
        self.L.require(P is not None, "division polynomial at infinity")
        x, y = P
        f, a, b = self.f, curve.a, curve.b
        x2, a2, b2 = f.square(x), f.square(a), f.square(b)
        x3, x4, x6, a3 = f.mul(x2, x), f.square(x2), f.cube(x2), f.mul(a2, a)
        w2 = f.mul(2, y)
        w3 = f.sub(f.add(f.add(f.mul(3, x4), f.mul(6, f.mul(a, x2))),
                              f.mul(12, f.mul(b, x))), a2)
        inside = f.add(f.add(x6, f.mul(5, f.mul(a, x4))), f.mul(20, f.mul(b, x3)))
        inside = f.sub(inside, f.mul(5, f.mul(a2, x2)))
        inside = f.sub(inside, f.mul(4, f.mul(f.mul(a, b), x)))
        inside = f.sub(f.sub(inside, f.mul(8, b2)), a3)
        w4 = f.mul(f.mul(4, y), inside)
        self.L.tick("cache_writes", 5)
        self.cache = {0: 0, 1: 1, 2: w2, 3: w3, 4: w4}
        self.inv_w2 = f.inv(w2)

    def value(self, n):
        self.L.tick("eds_requests")
        self.L.tick("comparisons")
        if n < 0:
            return self.f.sub(0, self.value(-n))
        self.L.tick("cache_reads")
        known = self.cache.get(n)
        if known is not None:
            self.L.tick("cache_hits")
            return known
        self.L.tick("eds_recurrences")
        self.L.tick("integer_divmods")
        m, parity = divmod(n, 2)
        f = self.f
        if parity:
            result = f.sub(f.mul(self.value(m + 2), f.cube(self.value(m))),
                           f.mul(self.value(m - 1), f.cube(self.value(m + 1))))
        else:
            inside = f.sub(f.mul(self.value(m + 2), f.square(self.value(m - 1))),
                           f.mul(self.value(m - 2), f.square(self.value(m + 1))))
            result = f.mul(f.mul(self.value(m), self.inv_w2), inside)
        self.L.tick("cache_writes")
        self.cache[n] = result
        return result


def phi(curve, P, exponent):
    """The WHOLE ratio is raised; no use of the nP identity to compute phi."""
    L, f = curve.ledger, curve.f
    L.tick("phi_evaluations")
    eds = DivisionPolynomial(curve, P)
    numerator = eds.value(curve.p - 1)
    denominator = eds.value(curve.p - 1 + curve.q)
    L.require(numerator != 0 and denominator != 0, "undefined phi ratio")
    return f.pow(f.mul(numerator, f.inv(denominator)), exponent)


def draw(rng, size, L):
    L.tick("random_draws")
    return rng.randrange(size)


def shuffled(values, seed, L):
    rng = random.Random(seed)
    L.tick("table_reads", len(values))
    L.tick("table_writes", len(values))
    result = list(values)
    for i in range(len(result) - 1, 0, -1):
        L.tick("loop_iterations")
        j = draw(rng, i + 1, L)
        L.tick("table_reads", 2)
        L.tick("table_writes", 2)
        result[i], result[j] = result[j], result[i]
    return result


def correlation(predictions, labels, L):
    L.require(len(predictions) == len(labels) and len(labels) > 0, "empty correlation")
    numerator = 0
    for i in range(len(labels)):
        L.tick("loop_iterations")
        numerator += char_product(L.read(predictions, i), L.read(labels, i), L)
        L.tick("integer_adds")
    return {"signed_numerator": numerator, "denominator": len(labels),
            "fixed_plus_sign_correct": (len(labels) + numerator) // 2,
            "orientation_sign": 1}


def run_case(curve, P, generator_seed, result):
    L, f, q = curve.ledger, curve.f, curve.q
    result.update({"P": P, "generator_seed": generator_seed, "complete": False,
                   "phase": "generator_validation", "rows": [], "correlations": []})
    before = L.snapshot()
    L.require(P is not None and P[1] != 0, "invalid prime-order generator")
    L.require(curve.scalar(P, q) is None, "generator does not have declared order")
    L.tick("integer_muls")
    L.tick("integer_divmods")
    exponent = inverse_integer((q * q) % (curve.p - 1), curve.p - 1, L)
    result["inverse_q_squared_mod_p_minus_1"] = exponent
    result["phase"] = "pointwise_phi_and_normalization"
    phi_P = phi(curve, P, exponent)
    c = f.character(phi_P)
    result.update({"phi_P": phi_P, "c": c})
    if "expected_c" in curve.spec:
        L.require(c == curve.spec["expected_c"], "tiny fixture character mismatch")
    eds = DivisionPolynomial(curve, P)
    c_from_W = f.character(f.mul(eds.value(curve.p - 1), eds.value(curve.p - 1 + q)))
    L.require(c_from_W == c, "character of ratio disagrees with c")
    L.tick("cache_writes")
    chars = {0: 0}
    Wchars = {}
    Q = None
    for k in range(1, q):
        L.tick("loop_iterations")
        Q = curve.add(Q, P)
        L.require(Q is not None, "premature identity in generator orbit")
        # Every tiny-fixture label is also checked by binary scalar multiplication.
        # Larger cases check public boundary indices; orbit additions label all k.
        if "expected_c" in curve.spec or k in (1, 2, q - 1):
            L.require(curve.scalar(P, k) == Q, "scalar/orbit mismatch")
        phi_Q = phi_P if k == 1 else phi(curve, Q, exponent)
        chi_phi = f.character(phi_Q)
        L.require(chi_phi in (-1, 1), "zero pointwise character")
        L.tick("cache_writes")
        chars[k] = chi_phi
        row = {"k": k, "Q": Q, "phi_Q": phi_Q, "chi_phi_Q": chi_phi, "indices": []}
        for n in (k, k + q):
            L.tick("loop_iterations")
            Wn = eds.value(n)
            L.require(Wn != 0, "unexpected nonidentity EDS zero")
            L.tick("integer_muls")
            correct = f.mul(f.pow(phi_P, n * n), Wn)
            L.require(correct == phi_Q, "corrected phi(nP) identity failed")
            sn = f.character(Wn)
            L.require(sn == char_product(chi_phi, sign_power(c, n, L), L),
                      "corrected c^n character identity failed")
            L.tick("cache_writes")
            Wchars[n] = sn
            L.tick("table_writes")
            row["indices"].append({"n": n, "W": Wn, "chi_W": sn,
                                   "value_identity": True, "character_identity": True})
        L.require(L.read(Wchars, k + q) == char_product(c, L.read(Wchars, k), L),
                  "character quasi-period failed")
        L.tick("table_writes")
        result["rows"].append(row)
    L.require(curve.add(Q, P) is None, "orbit did not close")
    result["normalization_checks"] = 2 * (q - 1)
    result["phase"] = "predeclared_correlations"
    for offsets in FAMILY:
        L.tick("loop_iterations")
        predictions, labels, excluded = [], [], []
        for k in range(q):
            L.tick("loop_iterations")
            wrapped = []
            for a in offsets:
                L.tick("integer_adds")
                L.tick("integer_divmods")
                L.tick("table_writes")
                wrapped.append((k + a) % q)
            L.tick("comparisons", len(wrapped))
            if 0 in wrapped:
                L.tick("table_writes")
                excluded.append(k)
                continue
            G, S = 1, 1
            for a, r in zip(offsets, wrapped):
                L.tick("loop_iterations")
                G = char_product(G, L.read(chars, r), L)
                # NO reduction of k+a modulo q in the EDS sequence.
                S = char_product(S, L.read(Wchars, k + a), L)
            L.tick("integer_muls")
            L.tick("integer_adds", len(offsets))
            n = len(offsets) * k + sum(offsets)
            expected_G = char_product(sign_power(c, n, L), S, L)
            L.require(G == expected_G, "wrapped phi/unwrapped EDS window mismatch")
            label = sign_power(-1, k, L)
            if c == -1:
                L.tick("integer_muls")
                L.tick("integer_adds")
                twisted = char_product(sign_power(-1, (len(offsets) + 1) * k + sum(offsets), L), S, L)
                L.require(char_product(G, label, L) == twisted, "c=-1 correlation identity failed")
            L.tick("table_writes", 2)
            predictions.append(G)
            labels.append(label)
        item = {"offsets": offsets, "product_parity": "odd" if len(offsets) % 2 else "even",
                "excluded_identity_indices": excluded, "excluded_mass_numerator": len(excluded),
                "excluded_mass_denominator": q, "eligible": len(labels),
                "eds_identity_checked": True, "c_class": c,
                "exact": correlation(predictions, labels, L), "shuffled_controls": []}
        for seed in SEEDS:
            control = {"seed": seed, **correlation(predictions, shuffled(labels, seed, L), L)}
            L.tick("table_writes")
            item["shuffled_controls"].append(control)
        L.tick("table_writes")
        result["correlations"].append(item)
    result.update({"complete": True, "phase": "complete", "event_vector": L.delta(before),
                   "eds_cache_size": len(eds.cache)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-events", type=int, default=1_000_000)
    parser.add_argument("--seconds", type=float, default=60.0)
    args = parser.parse_args()
    if not (0 < args.max_events <= 1_000_000 and 0 < args.seconds <= 60):
        parser.error("caps must be positive and no larger than 1M events / 60 seconds")
    L = Ledger(args.max_events, args.seconds)
    output = {"protocol": "H002 A1 EDS diagnostic pre-run v1", "diagnostic_not_solver": True,
              "verified_improvement": "NONE", "seeds": SEEDS, "predeclared_family": FAMILY,
              "fixtures": FIXTURES, "synthetic_curves": SYNTHETIC,
              "event_limit": L.limit, "seconds_limit": L.seconds,
              "complete": False, "curves": [], "cases": [],
              "sign_rule": "fixed +1; report signed correlations, no test-label sign selection"}
    active_before = None
    try:
        for spec in FIXTURES + SYNTHETIC:
            before = L.snapshot()
            curve = Curve(spec, L)
            curve_record = {"name": spec["name"], "parameters": spec, "validated": False}
            output["curves"].append(curve_record)
            points = curve.validate()
            curve_record.update({"validated": True, "point_count": len(points) + 1,
                                 "event_vector": L.delta(before)})
            generators = (None,) if "P" in spec else SEEDS
            for seed in generators:
                active_before = L.snapshot()
                result = {"curve": spec["name"], "complete": False, "phase": "generator_choice"}
                output["cases"].append(result)
                if seed is None:
                    P = spec["P"]
                    L.tick("comparisons", len(points))
                    L.require(P in points, "fixed fixture point is off curve")
                else:
                    rng = random.Random(seed)
                    P = L.read(points, draw(rng, len(points), L))
                run_case(curve, P, seed, result)
                result["event_vector"] = L.delta(active_before)
        output["complete"] = True
        output["status"] = "complete_diagnostic"
    except BudgetStop as exc:
        output.update({"status": "incomplete_budget_stop", "stop_reason": str(exc)})
    except Exception as exc:
        output.update({"status": "incomplete_validation_failure",
                       "stop_reason": type(exc).__name__ + ": " + str(exc)})
    if output["cases"] and not output["cases"][-1]["complete"] and active_before is not None:
        output["cases"][-1]["partial_event_vector"] = L.delta(active_before)
    output.update({"total_event_vector": L.snapshot(), "total_events": L.total,
                   "elapsed_seconds": time.monotonic() - L.started,
                   "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "requested_case_count": len(FIXTURES) + len(SYNTHETIC) * len(SEEDS),
                   "completed_case_count": sum(case["complete"] for case in output["cases"])})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({k: output[k] for k in ("status", "total_events", "elapsed_seconds",
                                           "completed_case_count", "verified_improvement")}))
    return 0 if output["complete"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
