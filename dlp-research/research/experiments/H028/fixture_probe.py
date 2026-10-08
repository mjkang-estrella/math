#!/usr/bin/env python3
"""Frozen H028 public fixture discovery. No numerical work without --execute.

Reuses reviewed affine formulas and expanded H018 modular-RAM operations.
Fixed fields/registers and instrumentation are administrative; dynamic accesses,
allocation cells, record materialization, comparisons and arithmetic are paid.
No discovery table is serialized or supplied to a later solver. Payload accounting
is an explicit packed model, NOT Python allocator bytes or bit-operation costs.
The frozen inputs use a 64-bit bounded-word arithmetic model: field moduli are
below 2^31, and field products below 2^62. Python integers implement these
abstract operations; their runtime is not being calibrated or equated to events.
"""
import argparse
import hashlib
import importlib.util
import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROTOCOL = HERE / "fixture_protocol.md"
KEY_SUPPORT = HERE / "key_probe.py"
BASE_SUPPORT = HERE.parent / "H018" / "bm_probe.py"
EVENT_CAP = 100_000_000
SECONDS_CAP = 55.0
EXPONENTS = (20, 25, 30)


class Failure(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Failure(message)


def put(m, row, key, value):
    m.tick("trace_field")
    row[key] = value


def pending(m, row, operation, **fields):
    row["pending"] = {"operation": operation, **fields}
    m.tick("trace_field", len(fields) + 1)


def point(m, p):
    if m.eq(p, None):
        return m.record(infinity=True)
    return m.record(infinity=False, x=p.x, y=p.y)


def bit_width(m, n):
    width = 0
    while not m.eq(n, 0):
        width = m.add(width, 1)
        n = m.shr(n, 1)
    return width


def isqrt_paid(m, n, row):
    require(not m.lt(n, 0), "negative integer square root")
    lo, hi = 0, m.add(n, 1)
    while m.lt(m.add(lo, 1), hi):
        pending(m, row, "integer_sqrt", n=n, lower=lo, upper=hi)
        mid = m.div(m.add(lo, hi), 2)
        if m.le(m.mul(mid, mid), n):
            lo = mid
        else:
            hi = mid
    require(m.le(m.mul(lo, lo), n), "sqrt lower bound")
    successor = m.add(lo, 1)
    require(m.lt(n, m.mul(successor, successor)), "sqrt upper bound")
    return lo


class Memory:
    """Temporary baby storage only; evidence storage reported separately.

    Each baby record models x,y,index and one infinity bit. Two reference arrays
    coexist during merge sort. Payload widths use p and B, plus null references.
    Lists are never copied to JSON. Allocation/deallocation cells are paid.
    """
    def __init__(self, m, p, width, row):
        self.m, self.row = m, row
        self.point_bits = m.add(m.mul(2, bit_width(m, m.sub(p, 1))),
                                m.add(bit_width(m, m.sub(width, 1)), 1))
        self.ref_bits = bit_width(m, width)
        self.slots = self.records = 0
        self.peak_bits = self.peak_slots = self.peak_records = 0
        self.allocated_slots = self.allocated_records = 0

    def update(self):
        # Instrumentation arithmetic does not feed the discovery algorithm.
        bits = self.slots * self.ref_bits + self.records * self.point_bits
        self.peak_bits = max(self.peak_bits, bits)
        self.peak_slots = max(self.peak_slots, self.slots)
        self.peak_records = max(self.peak_records, self.records)
        self.row["temporary_storage"] = {
            "live_reference_slots": self.slots, "live_baby_records": self.records,
            "peak_packed_payload_bits": self.peak_bits,
            "peak_reference_slots": self.peak_slots, "peak_baby_records": self.peak_records,
            "allocated_reference_slots": self.allocated_slots,
            "allocated_baby_records": self.allocated_records,
            "bits_per_baby_record": self.point_bits, "bits_per_reference": self.ref_bits,
            "excludes_active_registers_and_evidence": True, "not_python_bytes": True}

    def append(self, array, value, baby=False):
        self.m.tick("allocation_cell", 1 + (4 if baby else 0))
        self.m.append(array, value)
        self.slots += 1
        self.allocated_slots += 1
        if baby:
            self.records += 1
            self.allocated_records += 1
        self.update()

    def release_slots(self, n):
        self.m.tick("deallocation_cell", n)
        self.slots -= n
        self.update()

    def release_all(self):
        self.m.tick("deallocation_cell", self.slots + 4 * self.records)
        self.slots = self.records = 0
        self.update()


def point_compare(m, a, b):
    # Total order: O first, then x then y. Exact points, no sign quotient.
    if m.eq(a, None):
        return 0 if m.eq(b, None) else -1
    if m.eq(b, None):
        return 1
    if m.lt(a.x, b.x):
        return -1
    if m.lt(b.x, a.x):
        return 1
    if m.lt(a.y, b.y):
        return -1
    if m.lt(b.y, a.y):
        return 1
    return 0


def record_le(m, a, b):
    order = point_compare(m, a["point"], b["point"])
    if m.eq(order, 0):
        return m.le(a["j"], b["j"])
    return m.lt(order, 0)


def merge_sort(m, array, n, memory, row):
    scratch = []
    j = 0
    while m.lt(j, n):
        pending(m, row, "sort_scratch_allocation", initialized=j, length=n)
        memory.append(scratch, None)
        j = m.add(j, 1)
    run = 1
    while m.lt(run, n):
        start = 0
        while m.lt(start, n):
            pending(m, row, "merge_sort", run_width=run, start=start, length=n)
            middle = m.add(start, run)
            if m.lt(n, middle):
                middle = n
            end = m.add(middle, run)
            if m.lt(n, end):
                end = n
            left, right, out = start, middle, start
            while m.lt(out, end):
                if m.lt(left, middle) and (not m.lt(right, end) or
                        record_le(m, m.read(array, left), m.read(array, right))):
                    m.write(scratch, out, m.read(array, left))
                    left = m.add(left, 1)
                else:
                    m.write(scratch, out, m.read(array, right))
                    right = m.add(right, 1)
                out = m.add(out, 1)
            start = end
        array, scratch = scratch, array
        run = m.mul(run, 2)
    memory.release_slots(n)
    scratch = None
    # Independent adjacent order audit is paid, not assumed from sorting.
    j = 1
    while m.lt(j, n):
        require(record_le(m, m.read(array, m.sub(j, 1)), m.read(array, j)), "sort order")
        j = m.add(j, 1)
    return array


def lower_bound(m, array, n, target, row):
    lo, hi = 0, n
    while m.lt(lo, hi):
        pending(m, row, "lower_bound", lower=lo, upper=hi)
        mid = m.div(m.add(lo, hi), 2)
        if m.lt(point_compare(m, m.read(array, mid)["point"], target), 0):
            lo = m.add(mid, 1)
        else:
            hi = mid
    return lo


def attempt(base, support, m, p, b, row):
    curve = support.Curve(base, m, p, 1, b, 0)
    f = curve.f
    m.phase = "curve_screen"
    pending(m, row, "discriminant")
    disc = f.add(4, f.mul(27, f.square(b)))
    put(m, row, "discriminant_core", disc)
    if m.eq(disc, 0):
        put(m, row, "status", "rejected_singular")
        return False
    exponent = m.div(m.add(p, 1), 4)
    g, x = None, 0
    m.phase = "point_selection"
    while m.lt(x, 64):
        candidate = {"x": x, "completed": False}
        m.append(row["point_attempts"], candidate); m.tick("trace_field", 2)
        pending(m, row, "point_candidate", x=x)
        rhs = f.add(f.add(f.mul(f.square(x), x), x), b)
        y = f.power(rhs, exponent)
        valid = not m.eq(y, 0) and m.eq(f.square(y), rhs)
        put(m, candidate, "rhs", rhs); put(m, candidate, "y", y)
        put(m, candidate, "valid", valid); put(m, candidate, "completed", True)
        if valid:
            g = support.Point(x, y)
            break
        x = m.add(x, 1)
    if m.eq(g, None):
        put(m, row, "status", "rejected_point_limit")
        return False
    curve.check(g)
    put(m, row, "G", point(m, g))
    m.phase = "hasse_setup"
    limit = isqrt_paid(m, m.mul(4, p), row)
    span = m.mul(2, limit)
    number = m.add(span, 1)
    width = isqrt_paid(m, number, row)
    if m.lt(m.mul(width, width), number):
        width = m.add(width, 1)
    require(m.le(number, m.mul(width, width)), "ceil sqrt upper")
    prev = m.sub(width, 1)
    require(m.lt(m.mul(prev, prev), number), "ceil sqrt lower")
    upper, lower = m.add(m.add(p, 1), limit), m.sub(m.add(p, 1), limit)
    put(m, row, "L", limit); put(m, row, "B", width)
    put(m, row, "hasse_lower", lower); put(m, row, "hasse_upper", upper)
    pending(m, row, "R_scalar", scalar=upper)
    r = curve.scalar(upper, g)
    pending(m, row, "D_scalar", scalar=width)
    d = curve.scalar(width, g)
    put(m, row, "R", point(m, r)); put(m, row, "D", point(m, d))
    memory = Memory(m, p, width, row)
    babies = []
    m.phase = "baby_generation"
    current, j = None, 0
    while m.lt(j, width):
        pending(m, row, "baby_generation", completed=j, next_index=j)
        memory.append(babies, m.record(point=current, j=j), baby=True)
        put(m, row, "babies_completed", m.add(j, 1))
        j = m.add(j, 1)
        if m.lt(j, width):
            current, _, _ = curve.add(current, g)
    m.phase = "baby_sort"
    babies = merge_sort(m, babies, width, memory, row)
    m.phase = "giant_search"
    negd = curve.neg(d)
    maximum = m.div(span, width)
    i, giant, candidate_q = 0, r, None
    while m.le(i, maximum):
        event = {"i": i, "completed": False}
        m.append(row["giant_rows"], event); m.tick("trace_field", 2)
        # Keep only the current point as partial state, never a giant table.
        put(m, row, "active_giant", point(m, giant))
        pending(m, row, "giant_lookup", i=i)
        where = lower_bound(m, babies, width, giant, row)
        put(m, event, "lower_bound", where)
        if m.lt(where, width):
            baby = m.read(babies, where)
            if m.eq(point_compare(m, baby["point"], giant), 0):
                u = m.add(m.mul(i, width), baby["j"])
                put(m, event, "j", baby["j"]); put(m, event, "u", u)
                if m.le(u, span):
                    candidate_q = m.sub(upper, u)
                    put(m, event, "valid_collision", True)
                    put(m, event, "completed", True)
                    break
                put(m, event, "out_of_range", True)
        put(m, event, "completed", True)
        i = m.add(i, 1)
        if m.le(i, maximum):
            pending(m, row, "giant_advance", next_i=i)
            giant, _, _ = curve.add(giant, negd)
    # No table may escape this attempt, including a successful one.
    memory.release_all()
    babies = None
    if m.eq(candidate_q, None):
        put(m, row, "status", "rejected_no_collision_requires_review")
        return False
    put(m, row, "candidate_q", candidate_q)
    m.phase = "order_certification"
    pending(m, row, "q_primality", q=candidate_q)
    prime = base.prime_trial(m, candidate_q)
    put(m, row, "q_prime", prime)
    if not prime:
        put(m, row, "status", "rejected_composite_annihilator")
        return False
    # Fresh calculations: candidate annihilator is never accepted as an order
    # merely because the BSGS collision occurred.
    q = candidate_q
    not_anomalous, large = not m.eq(q, p), m.lt(3, q)
    nonidentity = not m.eq(g, None)
    nonsingular = not m.eq(f.add(4, f.mul(27, f.square(b))), 0)
    pending(m, row, "fresh_q_scalar", q=q)
    qg = curve.scalar(q, g)
    annihilates = m.eq(qg, None)
    in_interval = m.le(lower, q) and m.le(q, upper)
    unique_multiple = m.lt(upper, m.mul(2, q))
    certificate = m.record(q_prime=prime, q_not_p=not_anomalous, q_gt_3=large,
        G_nonidentity=nonidentity, nonsingular=nonsingular, qG=point(m, qg),
        annihilates=annihilates, in_hasse_interval=in_interval,
        unique_positive_multiple=unique_multiple)
    put(m, row, "certificate", certificate)
    require(large and nonidentity and nonsingular and annihilates and in_interval and unique_multiple,
            "prime annihilator contradicts independent certificate checks")
    accepted = prime and not_anomalous and large and nonidentity and nonsingular and annihilates and in_interval and unique_multiple
    put(m, row, "status", "accepted" if accepted else "rejected_certificate")
    return accepted


def discover(base, support, m, exponent, size):
    m.phase = "prime_search"
    value, j = 1, 0
    while m.lt(j, exponent):
        value = m.mul(value, 2)
        j = m.add(j, 1)
    t, selected = 0, None
    while m.lt(t, 4096):
        p = m.add(m.add(value, 3), m.mul(4, t))
        row = {"t": t, "p": p, "completed": False}
        m.append(size["prime_attempts"], row); m.tick("trace_field", 3)
        pending(m, size, "p_primality", t=t, p=p)
        prime = base.prime_trial(m, p)
        put(m, row, "prime", prime); put(m, row, "completed", True)
        if prime:
            selected = p
            break
        t = m.add(t, 1)
    if m.eq(selected, None):
        put(m, size, "status", "inconclusive_prime_limit")
        put(m, size, "pending", None)
        return
    p = selected
    require(m.eq(m.rem(p, 4), 3), "selected p residue")
    put(m, size, "p", p)
    b = 1
    while m.le(b, 64):
        m.phase = "curve_attempt_setup"
        row = {"b": b, "status": "in_progress", "pending": None,
               "point_attempts": [], "giant_rows": [], "babies_completed": 0}
        m.append(size["curve_attempts"], row); m.tick("trace_field", 6)
        pending(m, size, "curve_attempt", b=b)
        start = m.total
        accepted = attempt(base, support, m, p, b, row)
        put(m, row, "pending", None)
        row["events_without_final_summary"] = m.total - start  # instrumentation
        if accepted:
            put(m, size, "fixture", m.record(p=p, A=1, B=b, q=row["candidate_q"], G=row["G"],
                certificate=row["certificate"]))
            put(m, size, "status", "accepted")
            put(m, size, "pending", None)
            return
        b = m.add(b, 1)
    put(m, size, "status", "inconclusive_curve_limit")
    put(m, size, "pending", None)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def execute():
    start = time.monotonic()
    report = {"status": "in_progress", "started_utc": datetime.now(timezone.utc).isoformat(),
        "event_cap": EVENT_CAP, "seconds_cap": SECONDS_CAP, "sizes": [],
        "pending": "controlled_support_import", "fixture_discovery_only": True,
        "tables_are_not_solver_advice": True,
        "administrative_hash_json_timer_instrumentation_excluded_but_walltime_included": True}
    m, base, support, code = None, None, None, 0
    try:
        base = load(BASE_SUPPORT, "h028_fixture_h018")
        base.EVENT_CAP, base.SECONDS_CAP = EVENT_CAP, SECONDS_CAP
        m = base.Meter()
        m.started = start
        support = load(KEY_SUPPORT, "h028_fixture_key_support")
        report["hashes"] = {"source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "protocol_sha256": hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(),
            "H018_support_sha256": hashlib.sha256(BASE_SUPPORT.read_bytes()).hexdigest(),
            "H028_support_sha256": hashlib.sha256(KEY_SUPPORT.read_bytes()).hexdigest()}
        m.check_time()
        i = 0
        while m.lt(i, 3):
            m.phase = "size_setup"
            e = m.read(EXPONENTS, i)
            size = {"exponent": e, "status": "in_progress", "pending": None,
                    "prime_attempts": [], "curve_attempts": []}
            m.append(report["sizes"], size); m.tick("trace_field", 5)
            pending(m, report, "size", exponent=e)
            discover(base, support, m, e, size)
            i = m.add(i, 1)
        # Administrative classification only, not a new search or certificate.
        coverage_failure = any(r.get("status") == "rejected_no_collision_requires_review"
            for s in report["sizes"] for r in s["curve_attempts"])
        if coverage_failure:
            report["status"], code = "completed_with_coverage_failure_requires_review", 3
        elif all(s["status"] == "accepted" for s in report["sizes"]):
            report["status"] = "completed_all_fixtures_certified"
        else:
            report["status"], code = "inconclusive_search_limits", 2
        report["pending"] = None
    except Exception as exc:
        if base is not None and isinstance(exc, base.Halt):
            report["status"], code = "inconclusive_cap", 2
            report["error"] = "Effective fixture guard: 100000000 events / 55 seconds"
            report["support_message_not_effective_limits"] = str(exc)
        elif (isinstance(exc, Failure) or
              (base is not None and isinstance(exc, base.Invalid)) or
              (support is not None and isinstance(exc, support.Failure))):
            report["status"], report["error"], code = "correctness_failure", str(exc), 3
        else:
            report["status"], report["error"], code = "implementation_error", type(exc).__name__ + ": " + str(exc), 4
    if m is not None:
        report["events"], report["phase_events"] = m.total, m.by_phase
        report["event_categories"], report["phase_event_categories"] = m.by_kind, m.by_phase_kind
        report["cap_hit"] = m.cap_hit
        report["allocation_model"] = {
            "temporary_allocation_cells_charged": m.by_kind.get("allocation_cell", 0),
            "temporary_deallocation_cells_charged": m.by_kind.get("deallocation_cell", 0),
            "evidence_fields_materialized_charged": m.by_kind.get("trace_field", 0),
            "dynamic_array_writes_charged": m.by_kind.get("array_write", 0),
            "evidence_counts_include_overwritten_fields_not_live_bytes": True,
            "temporary_peak_payload_per_curve_recorded_separately": True}
    report["ended_utc"] = datetime.now(timezone.utc).isoformat()
    report["elapsed_before_json_seconds"] = time.monotonic() - start
    report["exit_code"] = code
    payload = json.dumps(report, indent=2, sort_keys=True)
    if time.monotonic() - start >= SECONDS_CAP:
        if code == 0:
            report["status"], code = "inconclusive_cap", 2
            report["error"] = "55-second guard crossed during final administration"
        report["cap_hit"] = "wall_time_during_reporting"
        report["exit_code"] = code
        payload = json.dumps(report, indent=2, sort_keys=True)
    sys.stdout.write(payload + "\n")
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    if not args.execute:
        parser.error("execution requires independent review and --execute")
    return execute()


if __name__ == "__main__":
    raise SystemExit(main())
