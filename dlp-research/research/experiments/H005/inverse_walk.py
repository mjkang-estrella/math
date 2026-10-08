#!/usr/bin/env python3
"""H005's one frozen, whole-attempt synthetic screen; no improvement claim.

Read inverse_walk_protocol.md before running. There are no warmups, self-tests,
random controls, hidden point tables, or parameter searches. The root runs this
only after independent review. Arithmetic instrumentation is an event model,
not CPU time or an exact count of Python/hardware instructions.

Field add/sub/mul count the arithmetic and its modular reduction separately;
their Python integer internals are NOT also counted as integer add/sub/mul.
Field inversion counts its call AND the actual binary-exponentiation operations.
Group calls similarly count both the call and their actual field operations.
Integer categories cover explicit scalar/coefficient/lattice/admission arithmetic.
Each explicit loop body, scalar/exponent bit, algorithm-table read/write and
explicit comparison is counted. Algorithm tables are the admission dictionary,
attempt dictionary, baby dictionary and expectation arithmetic dictionaries;
control/output records are instrumentation bookkeeping. Loop iteration events
include Python iterator advancement; tuple unpacking/indexing, ordinary
assignments, allocation, hashing, source hashing, ledger bookkeeping,
serialization/exception formatting and
interpreter dispatch are excluded. Executed expectation arithmetic is charged in
its own diagnostic metadata phase, separate from either solver's event vector.
Stored records report dictionary entries (not bytes); point temporaries and the
fixed setup points are separately documented. These nested events are deliberately
different categories, never an invented weighted CPU-work total.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import time


P, A, B, Q_ORDER = 59, 28, 27, 73
GENERATOR, TARGET = (34, 35), (4, 47)
TRANSITION_CAP, BABY_M, GIANT_MAX = 18, 6, 6
MAX_EVENTS, MAX_SECONDS = 1_000_000, 60.0


class BudgetStop(Exception):
    pass


class Ledger:
    def __init__(self, events, seconds):
        self.limit, self.seconds = events, seconds
        self.started = time.monotonic()
        self.total, self.counts = 0, Counter()

    def check(self):
        if time.monotonic() - self.started >= self.seconds:
            raise BudgetStop("global monotonic-time cap exhausted")

    def tick(self, category, amount=1):
        self.check()
        if self.total + amount > self.limit:
            raise BudgetStop("global instrumented-event cap exhausted")
        self.counts[category] += amount
        self.total += amount

    def eq(self, x, y):
        self.tick("comparisons")
        return x == y

    def lt(self, x, y):
        self.tick("comparisons")
        return x < y

    def require(self, condition, message):
        self.tick("comparisons")
        if not condition:
            raise ArithmeticError(message)

    def add(self, x, y):
        self.tick("integer_adds")
        return x + y

    def sub(self, x, y):
        self.tick("integer_subs")
        return x - y

    def mul(self, x, y):
        self.tick("integer_muls")
        return x * y

    def mod(self, x, n):
        self.tick("integer_divmods")
        return x % n

    def divmod(self, x, n):
        self.tick("integer_divmods")
        return divmod(x, n)

    def neg(self, x):
        self.tick("integer_negations")
        return -x

    def abs(self, x):
        self.tick("integer_absolute_values")
        return abs(x)

    def bit(self, n):
        self.tick("integer_bit_tests")
        return n & 1

    def shift(self, n):
        self.tick("integer_shifts")
        return n >> 1

    def left_shift(self, n, bits):
        self.tick("integer_left_shifts")
        return n << bits

    def read(self, table, key):
        self.tick("table_reads")
        return table.get(key)

    def write(self, table, key, value):
        self.tick("table_writes")
        table[key] = value

    def snapshot(self):
        return dict(self.counts)

    def delta(self, before):
        return {k: self.counts[k] - before.get(k, 0) for k in sorted(self.counts)
                if self.counts[k] != before.get(k, 0)}

    def lex_less(self, x, y):
        for left, right in zip(x, y):
            self.tick("loop_iterations")
            if not self.eq(left, right):
                return self.lt(left, right)
        return False


class Field:
    def __init__(self, p, ledger):
        self.p, self.L = p, ledger

    def reduce(self, x):
        self.L.tick("field_reductions")
        return x % self.p

    def add(self, x, y):
        self.L.tick("field_adds")
        return self.reduce(x + y)

    def sub(self, x, y):
        self.L.tick("field_subs")
        return self.reduce(x - y)

    def mul(self, x, y):
        self.L.tick("field_muls")
        return self.reduce(x * y)

    def inv(self, x):
        L = self.L
        L.tick("field_inversions")
        L.require(not L.eq(x, 0), "field inversion of zero")
        exponent, result, base = L.sub(self.p, 2), 1, x
        while not L.eq(exponent, 0):
            L.tick("loop_iterations")
            L.tick("exponent_bits")
            if not L.eq(L.bit(exponent), 0):
                result = self.mul(result, base)
            exponent = L.shift(exponent)
            if not L.eq(exponent, 0):
                base = self.mul(base, base)
        return result


def integer_inverse(x, modulus, L):
    """Explicit extended Euclid; no built-in modular pow/inverse."""
    L.tick("integer_inversions")
    old_r, r, old_t, t = modulus, L.mod(x, modulus), 0, 1
    while not L.eq(r, 0):
        L.tick("loop_iterations")
        quotient, remainder = L.divmod(old_r, r)
        old_r, r = r, remainder
        old_t, t = t, L.sub(old_t, L.mul(quotient, t))
    L.require(L.eq(old_r, 1), "integer inverse does not exist")
    return L.mod(old_t, modulus)


def is_prime(n, L):
    if L.lt(n, 2):
        return False
    divisor = 2
    while not L.lt(n, L.mul(divisor, divisor)):
        L.tick("loop_iterations")
        if L.eq(L.mod(n, divisor), 0):
            return False
        divisor = L.add(divisor, 1)
    return True


class Curve:
    def __init__(self, ledger):
        self.L, self.f = ledger, Field(P, ledger)

    def neg(self, point):
        self.L.tick("group_negations")
        if self.L.eq(point, None):
            return None
        return point[0], self.f.sub(0, point[1])

    def add(self, left, right):
        L, f = self.L, self.f
        L.tick("group_additions")
        if L.eq(left, None):
            return right
        if L.eq(right, None):
            return left
        x, y = left
        u, v = right
        if L.eq(x, u):
            if L.eq(f.add(y, v), 0):
                return None
            L.require(L.eq(y, v), "equal x with inconsistent ordinate")
            numerator = f.add(f.mul(3, f.mul(x, x)), A)
            denominator = f.mul(2, y)
        else:
            numerator, denominator = f.sub(v, y), f.sub(u, x)
        slope = f.mul(numerator, f.inv(denominator))
        xx = f.sub(f.sub(f.mul(slope, slope), x), u)
        yy = f.sub(f.mul(slope, f.sub(x, xx)), y)
        return xx, yy

    def scalar(self, point, scalar):
        L = self.L
        L.tick("scalar_multiplications")
        L.require(not L.lt(scalar, 0), "negative scalar")
        result = None
        while not L.eq(scalar, 0):
            L.tick("loop_iterations")
            L.tick("scalar_bits")
            if not L.eq(L.bit(scalar), 0):
                result = self.add(result, point)
            scalar = L.shift(scalar)
            if not L.eq(scalar, 0):
                point = self.add(point, point)
        return result

    def rhs(self, x):
        f = self.f
        return f.add(f.add(f.mul(f.mul(x, x), x), f.mul(A, x)), B)

    def on_curve(self, point):
        L, f = self.L, self.f
        L.require(not L.eq(point, None), "admission point is identity")
        x, y = point
        L.require(not L.lt(x, 0) and L.lt(x, P), "noncanonical x")
        L.require(not L.lt(y, 0) and L.lt(y, P), "noncanonical y")
        L.require(L.eq(f.mul(y, y), self.rhs(x)), "point is off curve")


def admission(curve):
    """O(p) squared-ordinate dictionary; never a solver point/log table."""
    L, f = curve.L, curve.f
    L.require(is_prime(P, L) and is_prime(Q_ORDER, L), "fixture prime failure")
    discriminant = f.add(f.mul(4, f.mul(f.mul(A, A), A)), f.mul(27, f.mul(B, B)))
    L.require(not L.eq(discriminant, 0), "singular fixture")
    L.require(not L.eq(P, Q_ORDER), "anomalous fixture")
    L.require(not L.eq(L.sub(L.add(P, 1), Q_ORDER), 0), "zero trace excluded")
    squares, peak = {}, 0
    for y in range(P):
        L.tick("loop_iterations")
        square = f.mul(y, y)
        old = L.read(squares, square)
        if L.eq(old, None):
            L.write(squares, square, 1)
            peak = L.add(peak, 1)
        else:
            L.write(squares, square, L.add(old, 1))
    cardinality = 1
    for x in range(P):
        L.tick("loop_iterations")
        multiplicity = L.read(squares, curve.rhs(x))
        if not L.eq(multiplicity, None):
            cardinality = L.add(cardinality, multiplicity)
    L.require(L.eq(cardinality, Q_ORDER), "curve cardinality differs from q")
    for point in (GENERATOR, TARGET):
        L.tick("loop_iterations")
        curve.on_curve(point)
        L.require(L.eq(curve.scalar(point, Q_ORDER), None), "qP is nonidentity")
    # Validate frozen bounds without a numeric library or a parameter search.
    ceil_sqrt = L.divmod(TRANSITION_CAP, 2)[0]
    L.require(L.lt(L.mul(L.sub(ceil_sqrt, 1), L.sub(ceil_sqrt, 1)), Q_ORDER),
              "transition cap lower square bound")
    L.require(not L.lt(L.mul(ceil_sqrt, ceil_sqrt), Q_ORDER),
              "transition cap upper square bound")
    L.require(not L.lt(Q_ORDER, L.mul(2, L.mul(BABY_M, BABY_M))), "baby lower bound")
    next_m = L.add(BABY_M, 1)
    L.require(L.lt(Q_ORDER, L.mul(2, L.mul(next_m, next_m))), "baby upper bound")
    stride = L.add(L.mul(2, BABY_M), 1)
    L.require(L.eq(GIANT_MAX, L.divmod(L.add(L.sub(Q_ORDER, 1), L.sub(stride, 1)),
                                    stride)[0]), "giant bound")
    return {"curve_cardinality": cardinality, "squared_ordinate_peak_records": peak,
            "enumerated_point_or_log_table": False}


def norm(vector, L):
    return L.add(L.mul(vector[0], vector[0]), L.mul(vector[1], vector[1]))


def dot(left, right, L):
    return L.add(L.mul(left[0], right[0]), L.mul(left[1], right[1]))


def shortest_norm(z, L):
    """Exact shortest nonzero squared length in u-z*v == 0 (mod p).

    (p,0),(z,1) is a basis of that index-p lattice. Swap to A=|a|^2 <=
    B=|b|^2. STOP at 2*|D| <= A, including half ties, D=<a,b>.
    Otherwise use nearest(D/A), ties toward zero, and replace b by b-n*a.
    This preserves the lattice. The replacement strictly decreases B because
    n has D's sign and 0 < |n|*A < 2*|D|. Swaps do not alter A+B, so the
    positive integer A+B strictly decreases at every reduction. Half ties
    cannot cause a same-norm cycle because we stop rather than reduce there.

    On exit, B >= A and |D| <= A/2. For a nonzero m*a+n*b, n=0 has norm >= A.
    If |n|=1, its norm is >= B+(m^2-|m|)*A >= A. If |n|>=2, perpendicular
    projection gives norm >= n^2*(B-D^2/A) >= 4*(3*A/4) >= A.
    Thus a is a shortest nonzero lattice vector. All decisions use integers.
    """
    a, b = (P, 0), (z, 1)
    while True:
        L.tick("loop_iterations")
        L.tick("lattice_iterations")
        aa, bb = norm(a, L), norm(b, L)
        if L.lt(bb, aa):
            a, b, aa, bb = b, a, bb, aa
        product = dot(a, b, L)
        absolute = L.abs(product)
        if not L.lt(aa, L.mul(2, absolute)):
            return aa
        quotient, remainder = L.divmod(absolute, aa)
        if L.lt(aa, L.mul(2, remainder)):
            quotient = L.add(quotient, 1)
        if L.lt(product, 0):
            quotient = L.neg(quotient)
        b = (L.sub(b[0], L.mul(quotient, a[0])),
             L.sub(b[1], L.mul(quotient, a[1])))


def score(point, L):
    L.tick("score_evaluations")
    if L.eq(point, None):
        return (0,)
    return (1, shortest_norm(point[0], L), point[0], point[1])


def verify(curve, scalar):
    curve.L.tick("answer_verifications")
    curve.L.require(curve.L.eq(curve.scalar(GENERATOR, scalar), TARGET),
                    "recovered scalar failed explicit point verification")


def candidate_setup(curve):
    L = curve.L
    inv2 = L.divmod(L.add(Q_ORDER, 1), 2)[0]
    half_g = curve.scalar(GENERATOR, inv2)
    return inv2, half_g, curve.neg(half_g), curve.neg(GENERATOR)


def candidate_attempt(curve, setup, restart, active):
    L = curve.L
    inv2, half_g, minus_half_g, minus_g = setup
    active["stage"] = "initial_state_formation"
    point = curve.add(TARGET, curve.scalar(GENERATOR, restart))
    a, b, t, seen, peak = 1, restart, 0, {}, 0
    cycle_length, recovered = None, None
    while True:
        L.tick("loop_iterations")
        active.update(stage="state_check", time=t, point=point, a=a, b=b,
                      dictionary_records=peak)
        if L.eq(point, None):
            numerator = L.neg(b)
            outcome = "identity_hit"
        elif L.eq(point, minus_g):
            numerator = L.sub(-1, b)
            outcome = "minus_generator_hit"
        else:
            old = L.read(seen, point)
            if not L.eq(old, None):
                old_t, old_a, old_b = old
                cycle_length = L.sub(t, old_t)
                denominator = L.mod(L.sub(old_a, a), Q_ORDER)
                if L.eq(denominator, 0):
                    outcome = "zero_denominator_cycle"
                    break
                recovered = L.mod(L.mul(L.sub(b, old_b),
                                          integer_inverse(denominator, Q_ORDER, L)), Q_ORDER)
                outcome = "useful_cycle"
                active["stage"] = "verification"
                active["recovered_scalar"] = recovered
                verify(curve, recovered)
                break
            if L.eq(t, TRANSITION_CAP):
                outcome = "timeout"
                break
            L.write(seen, point, (t, a, b))
            peak = L.add(peak, 1)
            active["dictionary_records"] = peak
            active["stage"] = "direct_halving_and_scores"
            u = curve.scalar(point, inv2)
            v = curve.add(u, minus_half_g)
            choose_u = L.lex_less(score(u, L), score(v, L))
            digit, point = (0, u) if choose_u else (1, v)
            a = L.mod(L.mul(inv2, a), Q_ORDER)
            b = L.mod(L.mul(inv2, L.sub(b, digit)), Q_ORDER)
            t = L.add(t, 1)
            continue
        recovered = L.mod(L.mul(numerator, integer_inverse(a, Q_ORDER, L)), Q_ORDER)
        active["stage"] = "verification"
        active["recovered_scalar"] = recovered
        verify(curve, recovered)
        break
    return {"restart": restart, "outcome": outcome, "transitions": t,
            "cycle_length": cycle_length, "recovered_scalar": recovered,
            "verified": not L.eq(recovered, None), "peak_dictionary_records": peak}


def point_key(point, L):
    L.tick("point_key_formations")
    return "identity" if L.eq(point, None) else point[0]


def signed_bsgs(curve, active):
    L = curve.L
    babies, point, peak = {}, None, 0
    for j in range(L.add(BABY_M, 1)):
        L.tick("loop_iterations")
        active.update(stage="baby_setup", baby_index=j, dictionary_records=peak)
        key = point_key(point, L)
        L.require(L.eq(L.read(babies, key), None), "duplicate baby x key")
        L.write(babies, key, (j, None if L.eq(point, None) else point[1]))
        peak = L.add(peak, 1)
        active["dictionary_records"] = peak
        if L.lt(j, BABY_M):
            point = curve.add(point, GENERATOR)
    active["stage"] = "giant_step_formation"
    step = curve.add(curve.add(point, point), GENERATOR)
    negative_step = curve.neg(step)
    stride = L.add(L.mul(2, BABY_M), 1)
    w = TARGET
    for i in range(L.add(GIANT_MAX, 1)):
        L.tick("loop_iterations")
        active.update(stage="giant_lookup", giant_index=i, point=w,
                      dictionary_records=peak)
        match = L.read(babies, point_key(w, L))
        if not L.eq(match, None):
            j, baby_y = match
            if L.eq(w, None):
                L.require(L.eq(j, 0), "identity baby has nonzero index")
                signed_j = 0
            elif L.eq(w[1], baby_y):
                signed_j = j
            else:
                L.require(L.eq(w[1], curve.f.sub(0, baby_y)), "baby sign mismatch")
                signed_j = L.neg(j)
            scalar = L.mod(L.add(L.mul(i, stride), signed_j), Q_ORDER)
            active["stage"] = "verification"
            active["recovered_scalar"] = scalar
            verify(curve, scalar)
            return {"recovered_scalar": scalar, "verified": True, "giant_index": i,
                    "peak_dictionary_records": peak, "baby_records": peak}
        if L.lt(i, GIANT_MAX):
            w = curve.add(w, negative_step)
    raise ArithmeticError("full-domain signed BSGS failed")


def exact_expectation(setup_vector, attempts, L):
    """Exact law for fixed Q; charge executed metadata, not hypothetical draws."""
    successes, summed = 0, {}
    for record in attempts:
        L.tick("loop_iterations")
        if L.eq(record["verified"], True):
            successes = L.add(successes, 1)
        for category, count in record["events"].items():
            L.tick("loop_iterations")
            old = L.read(summed, category)
            if L.eq(old, None):
                old = 0
            L.write(summed, category, L.add(old, count))
    if L.eq(successes, 0):
        return {"successes": 0, "attempts": Q_ORDER, "success_probability": [0, Q_ORDER],
                "expected_solver_events": "infinite", "sampler": "infinite"}
    bits, remaining = 0, L.sub(Q_ORDER, 1)
    while not L.eq(remaining, 0):
        L.tick("loop_iterations")
        bits = L.add(bits, 1)
        remaining = L.shift(remaining)
    raw_numerator = L.left_shift(1, bits)
    bit_numerator = L.mul(bits, raw_numerator)
    # Divide these numerators by q for per-attempt expectations, and by the
    # success count for solve expectations (because u=successes/q). Bits are
    # independent ideal unbiased primitives. No actual entropy calls occur.
    sampler_numerators = {"comparisons": raw_numerator,
                          "loop_iterations": L.add(raw_numerator, bit_numerator),
                          "unbiased_bits": bit_numerator,
                          "integer_left_shifts": bit_numerator,
                          "integer_ors": bit_numerator}
    categories = set(setup_vector) | set(summed) | set(sampler_numerators)
    # Unreduced numerator/denominator pairs preserve exactness with no float.
    expected, expected_attempt = {}, {}
    for category in sorted(categories):
        L.tick("loop_iterations")
        values = []
        for table in (setup_vector, summed, sampler_numerators):
            L.tick("loop_iterations")
            value = L.read(table, category)
            values.append(0 if L.eq(value, None) else value)
        setup_cost, attempt_sum, sampling = values
        per_attempt_numerator = L.add(attempt_sum, sampling)
        numerator = L.add(L.mul(setup_cost, successes), per_attempt_numerator)
        L.write(expected, category, [numerator, successes])
        L.write(expected_attempt, category, [per_attempt_numerator, Q_ORDER])
    sampler_attempt, sampler_solve = {}, {}
    for category, numerator in sampler_numerators.items():
        L.tick("loop_iterations")
        L.write(sampler_attempt, category, [numerator, Q_ORDER])
        L.write(sampler_solve, category, [numerator, successes])
    return {"successes": successes, "attempts": Q_ORDER,
            "success_probability": [successes, Q_ORDER],
            "sum_all_attempt_event_vectors": dict(sorted(summed.items())),
            "expected_attempt_events_including_sampler": expected_attempt,
            "expected_solver_events": expected,
            "formula": "setup + sum_all_restart_costs / successes + sampler_per_attempt / u",
            "law_scope": "uniform restart for THIS fixed Q; not a uniform-secret or curve average",
            "sampler": {"unbiased_bits_per_raw_draw": bits,
                        "expected_raw_draws_per_attempt": [raw_numerator, Q_ORDER],
                        "expected_bits_per_attempt": [bit_numerator, Q_ORDER],
                        "expected_raw_draws_per_solve": [raw_numerator, successes],
                        "expected_bits_per_solve": [bit_numerator, successes],
                        "expected_event_vector_per_attempt": sampler_attempt,
                        "expected_event_vector_per_solve": sampler_solve,
                        "runtime_draws_executed": 0,
                        "note": "One comparison and draw-loop per draw; one unbiased bit, left shift, OR and bit-loop per bit. Expectations are not actual diagnostic ledger events."}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--max-events", type=int, default=MAX_EVENTS)
    parser.add_argument("--max-seconds", type=float, default=MAX_SECONDS)
    args = parser.parse_args()
    if not 0 < args.max_events <= MAX_EVENTS:
        parser.error("--max-events may only lower the 1,000,000 cap")
    if not 0 < args.max_seconds <= MAX_SECONDS:
        parser.error("--max-seconds may only lower the 60-second cap")
    source = Path(__file__).resolve()
    protocol = source.with_name("inverse_walk_protocol.md")
    if args.output.resolve() in (source, protocol):
        parser.error("output must not overwrite source or protocol")
    L = Ledger(args.max_events, args.max_seconds)
    result = {"status": "incomplete", "scope": "one selected tiny synthetic full-attempt screen",
              "verified_improvement": "NONE", "fixture": {"p": P, "a": A, "b": B,
              "q": Q_ORDER, "G": GENERATOR, "Q": TARGET},
              "bounds": {"T": TRANSITION_CAP, "baby_m": BABY_M, "giant_max": GIANT_MAX,
                         "events": args.max_events, "seconds": args.max_seconds},
              "source_sha256": None, "protocol_sha256": None,
              "completed_attempts": [], "phase_event_vectors": {},
              "memory_scope": "Peak dictionary records; candidate also holds 3 setup points and O(1) point/vector temporaries; baseline O(1) point temporaries.",
              "accounting_scope": __doc__,
              "gate_verdict": "unassessed; no incomplete-domain expectation permitted"}
    curve = Curve(L)
    active = {"phase": "provenance_hashing"}
    before = L.snapshot()
    exit_code = 2
    try:
        result["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        result["protocol_sha256"] = hashlib.sha256(protocol.read_bytes()).hexdigest()
        active = {"phase": "admission"}
        result["admission"] = admission(curve)
        result["phase_event_vectors"]["admission"] = L.delta(before)
        active = {"phase": "candidate_setup"}
        before = L.snapshot()
        setup = candidate_setup(curve)
        setup_vector = L.delta(before)
        result["phase_event_vectors"]["candidate_setup"] = setup_vector
        for restart in range(Q_ORDER):
            active = {"phase": "diagnostic_restart_enumeration", "restart": restart}
            before = L.snapshot()
            L.tick("loop_iterations")
            driver = result["phase_event_vectors"].setdefault("diagnostic_restart_enumeration", {})
            driver["loop_iterations"] = driver.get("loop_iterations", 0) + 1
            active = {"phase": "candidate_attempt", "restart": restart}
            before = L.snapshot()
            record = candidate_attempt(curve, setup, restart, active)
            record["events"] = L.delta(before)
            result["completed_attempts"].append(record)
        active = {"phase": "diagnostic_expectation_metadata"}
        before = L.snapshot()
        result["candidate_expected_work"] = exact_expectation(setup_vector, result["completed_attempts"], L)
        result["phase_event_vectors"]["diagnostic_expectation_metadata"] = L.delta(before)
        active = {"phase": "signed_bsgs"}
        before = L.snapshot()
        result["reference"] = signed_bsgs(curve, active)
        result["phase_event_vectors"]["signed_bsgs"] = L.delta(before)
        active = {"phase": "completion_cap_check"}
        before = L.snapshot()
        L.check()
        result["status"] = "complete"
        result["gate_verdict"] = "categorywise costs ready for review; single-profile completion supports no improvement claim"
        active = {"phase": "complete"}
        before = L.snapshot()
        exit_code = 0
    except Exception as error:
        result["error"] = {"type": type(error).__name__, "message": str(error)}
    result["active_phase"] = active
    result["partial_phase_event_vector"] = L.delta(before)
    result["total_event_vector"] = dict(sorted(L.counts.items()))
    result["total_instrumented_events"] = L.total
    result["elapsed_seconds_through_computation"] = time.monotonic() - L.started
    reconciled = Counter()
    for vector in result["phase_event_vectors"].values():
        reconciled.update(vector)
    for record in result["completed_attempts"]:
        reconciled.update(record["events"])
    reconciled.update(result["partial_phase_event_vector"])
    result["reconciliation"] = {"sum_partition_events": sum(reconciled.values()),
                                "equals_global_vector": reconciled == L.counts,
                                "equals_global_total": sum(reconciled.values()) == L.total}
    if not result["reconciliation"]["equals_global_vector"]:
        result["status"], exit_code = "incomplete", 2
        result["reconciliation_error"] = "phase accounting does not reconcile"
    # Report construction, hashes and writing are excluded event work. The cap
    # clock is never restarted. A write error remains a nonzero process exit.
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
