#!/usr/bin/env python3
"""H018 v2 fixture-only extension: implementation/review, NOT execution approval.

Future approved invocation: python3 -B bm_probe_extension.py --approved-execution
Imports immutable v1 arithmetic/BM. No alternate engine, feature, or secret.
Administrative provenance/JSON are excluded from RAM events, as in v1; their
wall time is included. Prior numerical data supplies no fixture input.
"""

from __future__ import annotations

import time

PROCESS_STARTED = time.monotonic()

import argparse
import hashlib
import json
import sys
from pathlib import Path

# Check before importing v1, so even an accidental invocation cannot create its
# bytecode cache. AST inspection does not execute this check or any imports.
if not sys.dont_write_bytecode:
    raise SystemExit("Use python3 -B; execution still needs separate root approval.")

import bm_probe as base


PRIOR_EVENTS = 71_755
EXPECTED_Q_COUNT = 39
MAX_ORDER_TESTS = 273
MAX_B = 8
AGGREGATE_SECONDS_CAP = 120.0
DIRECTORY = Path(__file__).resolve().parent
PROTOCOL_PATH = DIRECTORY.parents[1] / "hypotheses/H018-bm-probe-v2.md"
PRIOR_OUTPUT_PATH = DIRECTORY / "initial_results.json"
PRIOR_SOURCE_PATH = DIRECTORY / "bm_probe.py"
PRIOR_PROTOCOL_PATH = base.PROTOCOL_PATH

# These are reservations for this declared extension, not changes to v1.
RESERVATIONS = {
    "prior_diagnostic": PRIOR_EVENTS,
    "selection_setup": 35_000,
    "extension_assertions": 1,
    "order_certification": 210_483,
    "primitive_w": 25_000,
    "orbit_scalar": 36_703,
    "features": 35_000,
    "bm": 400_000,
    "controls": 35_000,
    "setup": 20_000,
}


def select_fixture(m, report):
    """Only copied algorithm; diff from v1 is deliberately small.

    Changes: enumerate the whole Hasse interval, assert exactly39 recertified
    q primes in its own one-event phase, b<=8, and <=273 order tests. Otherwise
    same discriminant/2-torsion/point/order rules. Never read prior q values.
    """
    m.phase = "selection_setup"
    if not base.prime_trial(m, base.P):
        raise base.Invalid("frozen p is not prime")
    q_primes = []
    q = 8011
    # V2 removes the v1 maximum-list-length guard: certify the entire interval.
    while m.le(q, 8373):
        if not m.eq(q, base.P) and base.prime_trial(m, q):
            m.append(q_primes, q)
        q = m.add(q, 2)
    report["q_candidates"] = q_primes
    m.phase = "extension_assertions"
    if not m.eq(len(q_primes), EXPECTED_Q_COUNT):
        raise base.Invalid("recertified prime count differs from frozen 39")
    m.phase = "selection_setup"
    report["selection_attempts"] = attempts = []
    order_tests = 0
    b = 1
    while m.le(b, MAX_B):
        curve = base.Curve(m, b)
        f = curve.f
        if m.eq(f.add(4, f.mul(27, f.square(b))), 0):
            m.append(attempts, m.record(b=b, outcome="singular"))
            b = m.add(b, 1)
            continue
        minus_one = f.sub(0, 1)
        at_minus_one = f.add(f.add(f.mul(f.square(minus_one), minus_one), minus_one), b)
        if m.eq(at_minus_one, 0):
            m.append(attempts, m.record(b=b, outcome="rational_two_torsion_at_minus_one"))
            b = m.add(b, 1)
            continue
        g = None
        x = 0
        while m.le(x, 15):
            h = f.add(f.add(f.mul(f.square(x), x), x), b)
            y = h
            j = 0
            while m.lt(j, 11):
                y = f.square(y)
                j = m.add(j, 1)
            if m.eq(f.square(y), h) and not m.eq(y, 0):
                other_y = m.sub(base.P, y)
                if m.lt(other_y, y):
                    y = other_y
                g = base.Point(x, y, 1)
                curve.check_affine(g)
                break
            x = m.add(x, 1)
        if m.eq(g, None):
            m.append(attempts, m.record(b=b, outcome="no_point_in_bounded_search"))
            b = m.add(b, 1)
            continue
        attempt = m.record(b=b, gx=g.x, gy=g.y, q_tests=[])
        m.append(attempts, attempt)
        qi = 0
        while m.lt(qi, len(q_primes)):
            if not m.lt(order_tests, MAX_ORDER_TESTS):
                raise base.Halt("fixture not found: global 273 extension order tests exhausted")
            q = m.read(q_primes, qi)
            m.phase = "order_certification"
            multiple = curve.scalar(q, g)
            is_zero = m.eq(multiple.z, 0)
            m.append(attempt["q_tests"], m.record(q=q, multiple_x=multiple.x,
                     multiple_y=multiple.y, multiple_z=multiple.z, is_zero=is_zero))
            order_tests = m.add(order_tests, 1)
            m.phase = "selection_setup"
            if is_zero:
                if not m.lt(8373, m.mul(2, q)):
                    raise base.Invalid("Hasse certificate condition failed")
                report["fixture"] = m.record(p=base.P, a=1, b=b, q=q, gx=g.x,
                    gy=g.y, order_tests=order_tests, hasse_lower=8011,
                    hasse_upper=8373, certificate="q prime; G != O; [q]G=O; 2q>8373")
                return curve, g, q
            qi = m.add(qi, 1)
        b = m.add(b, 1)
    raise base.Halt("fixture not found: eight public curves exhausted; no further extension")


def provenance(report):
    """Administrative integrity only; never return prior fixture/prime data."""
    raw_prior = PRIOR_OUTPUT_PATH.read_bytes()
    prior = json.loads(raw_prior)
    raw_source = PRIOR_SOURCE_PATH.read_bytes()
    raw_old_protocol = PRIOR_PROTOCOL_PATH.read_bytes()
    raw_new_protocol = PROTOCOL_PATH.read_bytes()
    old_source_hash = hashlib.sha256(raw_source).hexdigest()
    old_protocol_hash = hashlib.sha256(raw_old_protocol).hexdigest()
    if (old_source_hash != "0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7"
            or old_protocol_hash != "6aea6695ec278f0804dcea3361a52d8d494bb1a3cf9f5559e73e74822a31094f"
            or hashlib.sha256(raw_prior).hexdigest() != "fc52157f888da32181c0b1ad749a965cc5539cf06f0e95fdefd26a00ee7843a0"):
        raise base.Invalid("v1 artifacts differ from independently audited fixed hashes")
    report["provenance"] = {
        "prior_commit": "124dba5",
        "prior_output_path": str(PRIOR_OUTPUT_PATH),
        "prior_output_sha256": hashlib.sha256(raw_prior).hexdigest(),
        "prior_source_sha256": old_source_hash,
        "prior_protocol_sha256": old_protocol_hash,
        "extension_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "extension_protocol_sha256": hashlib.sha256(raw_new_protocol).hexdigest(),
    }
    if (prior.get("events") != PRIOR_EVENTS
            or prior.get("protocol") != "H018-bm-probe-v1"
            or prior.get("status") != "inconclusive"
            or prior.get("halt_reason") != "fixture not found: global 96 order tests exhausted"
            or prior.get("cap_hit") is not None
            or prior.get("controls_completed") is not False
            or prior.get("planted_control_validated") is not False
            or prior.get("feature_sampling_completed") is not False
            or prior.get("controls") != []
            or prior.get("features") != []
            or prior.get("fixture") is not None):
        raise base.Invalid("prior output does not match the declared selection-only failure")
    if (prior.get("implementation_sha256") != old_source_hash
            or prior.get("protocol_sha256") != old_protocol_hash):
        raise base.Invalid("immutable v1 source/protocol hash mismatch")
    prior_elapsed = prior.get("elapsed_before_json_encoding_seconds")
    if (not isinstance(prior_elapsed, (int, float))
            or not 0 <= prior_elapsed < base.SECONDS_CAP):
        raise base.Invalid("prior recorded elapsed time is missing or outside its guard")
    report["prior_recorded_elapsed_before_json_encoding_seconds"] = prior_elapsed
    report["prior_events_carried_as_lump_not_current_curve_operations"] = PRIOR_EVENTS
    report["prior_phase_events_for_reference_only"] = prior.get("phase_events")
    return prior_elapsed


def execute():
    m = base.Meter()
    # Include this driver's imports, provenance and argument parsing in the
    # new process wall guard. Do not change base's 60-second guard or event cap.
    m.started = PROCESS_STARTED
    m.phase = "prior_diagnostic"
    report = {
        "protocol": "H018-bm-probe-v2",
        "implementation_status": "review-only; separate execution approval required",
        "ledger_unit": "same bounded-word modular RAM events as immutable H018 v1",
        "cumulative_event_cap": base.EVENT_CAP,
        "prior_event_charge_required": PRIOR_EVENTS,
        "maximum_current_events": 928245,
        "current_process_seconds_cap": base.SECONDS_CAP,
        "aggregate_two_process_seconds_cap": AGGREGATE_SECONDS_CAP,
        "declared_wall_budget_extension": "two independently guarded 60-second processes, not an automatic reset",
        "planted_control_validated": False,
        "controls_completed": False,
        "feature_sampling_completed": False,
        "status": "in_progress",
        "provenance_and_encoding_excluded_from_event_count": True,
        "administrative_wall_time_included": True,
        "cumulative_paper_phase_reservations": RESERVATIONS,
        "cumulative_paper_total": 868942,
        "no_further_fixture_extensions": True,
    }
    control_states = []
    feature_states = []
    prior_elapsed = None
    prior_debited = 0
    try:
        # FIRST algorithmic ledger action; no new fixture work precedes carry.
        m.tick("prior_run_events", PRIOR_EVENTS)
        prior_debited = PRIOR_EVENTS
        m.phase = "setup"
        prior_elapsed = provenance(report)
        m.check_time()
        curve, g, q = select_fixture(m, report)
        w = base.primitive_element(m, q, report)
        base.controls(m, q, w, report, control_states)
        base.run_features(m, curve, g, q, w, report, feature_states)
        report["status"] = "completed_finite_diagnostic_only"
    except base.Halt as exc:
        report["status"] = "inconclusive"
        report["halt_reason"] = str(exc)
    except base.Invalid as exc:
        report["status"] = "invalid_or_failed_implementation_preflight"
        report["halt_reason"] = str(exc)
    except Exception as exc:
        report["status"] = "implementation_error"
        report["halt_reason"] = type(exc).__name__ + ": " + str(exc)

    # Administrative snapshots: no completion of interrupted algebraic work.
    report["controls"] = [state.administrative_snapshot() for state in control_states]
    report["features"] = [state.administrative_snapshot() for state in feature_states]
    # Even if startup exhausts wall time before the carry tick can commit,
    # the real prior experiment still cost 71755. Distinguish that edge case
    # from what this meter managed to debit; no new algorithm runs before it.
    report["cumulative_events"] = PRIOR_EVENTS + m.total - prior_debited
    report["meter_recorded_events_including_successful_prior_debit"] = m.total
    report["prior_events_actually_debited"] = prior_debited
    report["current_events"] = m.total - prior_debited
    report["cumulative_phase_events"] = m.by_phase
    report["cumulative_event_categories_with_prior_lump"] = m.by_kind
    report["cumulative_phase_event_categories"] = m.by_phase_kind
    report["current_phase_events"] = {
        phase: count for phase, count in m.by_phase.items() if phase != "prior_diagnostic"
    }
    report["current_event_categories"] = {
        kind: count for kind, count in m.by_kind.items() if kind != "prior_run_events"
    }
    report["observed_current_max_projective_step_events"] = m.step_max
    report["cap_hit"] = m.cap_hit
    report["phase_reservation_overruns"] = {
        phase: count - RESERVATIONS.get(phase, 0)
        for phase, count in m.by_phase.items()
        if count > RESERVATIONS.get(phase, 0)
    }
    elapsed = time.monotonic() - m.started
    report["current_elapsed_before_json_encoding_seconds"] = elapsed
    if prior_elapsed is not None:
        report["sum_of_recorded_pre_json_elapsed_seconds"] = prior_elapsed + elapsed
    payload = json.dumps(report, indent=2, sort_keys=True)
    elapsed_after_encoding = time.monotonic() - m.started
    if elapsed_after_encoding >= base.SECONDS_CAP and report["cap_hit"] is None:
        report["status"] = "inconclusive"
        report["cap_hit"] = "wall_time_during_reporting"
        report["halt_reason"] = "new process 60-second guard exceeded during administrative reporting"
        report["current_elapsed_after_initial_json_encoding_seconds"] = elapsed_after_encoding
        payload = json.dumps(report, indent=2, sort_keys=True)
    sys.stdout.write(payload + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--approved-execution", action="store_true",
                        help="acknowledge separate root approval; this flag cannot grant it")
    args = parser.parse_args()
    if not args.approved_execution:
        parser.error("review-only: extension execution requires separate root approval")
    execute()


if __name__ == "__main__":
    main()
