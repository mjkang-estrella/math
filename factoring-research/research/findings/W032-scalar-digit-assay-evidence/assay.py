"""Single frozen execution; invoked only by launch_once.py."""
import hashlib
import json
import platform
import sys
import time
from collections import Counter
from pathlib import Path

import candidate
import reference
from meter import Meter, StopAssay


ROOT = Path(__file__).resolve().parent


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def summarize(records):
    # Output/instrumentation counters, not arithmetic on candidate operands.
    groups = {}
    for rec in records:
        key = str(rec["N"])
        group = groups.setdefault(key, {
            "total_cases": 0, "statuses": Counter(), "initial_statuses": Counter(),
            "initial_proper_cases": [], "unit_cases": [], "identity_counts": {},
            "matrix_case_indices": [], "digits": {}, "unit_any_digit_proper": [],
            "unit_digit_3_or_4_proper": [], "unit_digit_3_or_4_only_proper": []})
        group["total_cases"] += 1
        group["statuses"][rec["status"]] += 1
        group["initial_statuses"][rec.get("initial_status", "not_reached")] += 1
        if rec.get("initial_status") == "initial_proper_factor":
            group["initial_proper_cases"].append({"index": rec["index"], "a": rec["a"],
                                                   "gcd": rec["initial_gcd"]})
        if rec.get("initial_status") == "unit":
            group["unit_cases"].append(rec["index"])
        for name, outcome in rec.get("identity_outcomes", {}).items():
            group["identity_counts"].setdefault(name, Counter())[str(outcome)] += 1
        if rec.get("matrix_reference") is not None:
            group["matrix_case_indices"].append(rec["index"])
        proper_r = []
        for digit in rec.get("digits", []):
            ds = group["digits"].setdefault(str(digit["r"]), {
                "observed": 0, "gcd_categories": Counter(), "proper_cases": [],
                "gcd_N_cases": [], "proper_factor_counts": Counter()})
            ds["observed"] += 1
            g = digit["gcd"]
            category = "gcd_1" if g == 1 else "gcd_N" if g == rec["N"] else "proper"
            ds["gcd_categories"][category] += 1
            case = {"index": rec["index"], "a": rec["a"], "d": digit["d"], "gcd": g}
            if category == "proper":
                ds["proper_cases"].append(case)
                ds["proper_factor_counts"][str(g)] += 1
                proper_r.append(digit["r"])
            elif category == "gcd_N":
                ds["gcd_N_cases"].append(case)
        if proper_r:
            group["unit_any_digit_proper"].append(rec["index"])
        if 3 in proper_r or 4 in proper_r:
            group["unit_digit_3_or_4_proper"].append(rec["index"])
            if 1 not in proper_r and 2 not in proper_r:
                group["unit_digit_3_or_4_only_proper"].append(rec["index"])
    return groups


def main():
    start = float(sys.argv[1])
    deadline = float(sys.argv[2])
    config = json.loads((ROOT / "cases.json").read_text())
    limits = config["limits"]
    m = Meter(ROOT / "events.jsonl", deadline, limits["events"])
    cases = config["cases"]
    records = [{**case, "status": "unstarted", "initial_status": "not_reached",
                "V": None, "digits": [], "identity_outcomes": {},
                "matrix_reference": None} for case in cases]
    setups = {}
    refs = {}
    current = None
    first_failure = None
    stop_reason = None
    completed_log = (ROOT / "records.jsonl").open("x")
    try:
        # Hashing and JSON parsing are administrative, inside the wall-time cap.
        frozen = json.loads((ROOT / "freeze-manifest.json").read_text())
        for entry in frozen["files"]:
            actual = hashlib.sha256((ROOT / entry["path"]).read_bytes()).hexdigest()
            m.check("frozen_input_hash", actual == entry["sha256"], entry["bytes"])
        m.check("fixed_trial_count", len(cases) == 155, len(cases))
        m.check("fixed_R_and_caps", config["Rmax"] == 4 and limits["events"] == 20000
                and limits["seconds"] == 60, config["Rmax"], limits["events"], limits["seconds"])
        for spec in config["groups"]:
            N = spec["N"]
            m.scope = "candidate_setup"
            setups[N] = candidate.public_setup(N, config["Rmax"], m)
            m.scope = "reference_setup"
            refs[N] = reference.setup_reference(N, config["Rmax"], setups[N],
                    spec["reference_factors"], bool(spec["matrix_reference_a"]), m)
        write_json(ROOT / "setup-results.json", {
            "candidate_public": setups, "reference_only": refs,
            "accounting": m.snapshot()})
        reference_cases = {(spec["N"], a) for spec in config["groups"]
                           for a in spec["matrix_reference_a"]}
        for rec in records:
            current = rec
            m.trial = rec["index"]
            m.scope = "candidate"
            rec["status"] = "running"
            rec["event_start_exclusive"] = m.events
            trial_start = time.monotonic()
            write_json(ROOT / "progress.json", rec)
            m.mark("trial_stage", rec["index"], rec["N"], rec["a"])
            candidate.run_case(rec["N"], rec["a"], config["Rmax"],
                               setups[rec["N"]], rec, m)
            rec["candidate_complete"] = True
            rec["candidate_elapsed_seconds"] = time.monotonic() - trial_start
            write_json(ROOT / "progress.json", rec)
            m.scope = "reference"
            reference.check_case(rec, setups[rec["N"]], refs[rec["N"]],
                                 (rec["N"], rec["a"]) in reference_cases, m)
            rec["status"] = "completed"
            rec["accounting"] = m.by_trial[m.trial]
            rec["event_end_inclusive"] = m.events
            rec["elapsed_seconds"] = time.monotonic() - trial_start
            completed_log.write(json.dumps(rec, sort_keys=True) + "\n")
            completed_log.flush()
            write_json(ROOT / "progress.json", rec)
            current = None
        m.check_time()
    except StopAssay as exc:
        stop_reason = exc.reason
        first_failure = exc.detail
        if current is not None:
            current["status"] = "failed" if exc.reason == "mismatch" else "stopped"
            current["stop_reason"] = exc.reason
            current["first_failure"] = exc.detail
            current["event_end_inclusive"] = m.events
            current["accounting"] = m.by_trial.get(m.trial, {"events": 0})
            current["elapsed_seconds"] = time.monotonic() - trial_start
    except Exception as exc:
        stop_reason = "implementation_error"
        first_failure = {"type": type(exc).__name__, "message": str(exc),
                         "trial": m.trial, "scope": m.scope, "pending": m.pending}
        if current is not None:
            current["status"] = "failed"
            current["stop_reason"] = stop_reason
            current["accounting"] = m.by_trial.get(m.trial, {"events": 0})
    finally:
        completed_log.close()
        m.log.close()
    result = {
        "run_count": 1, "status": "completed" if stop_reason is None else stop_reason,
        "first_failure": first_failure, "limits": limits,
        "elapsed_seconds": time.monotonic() - start,
        "python": sys.version, "platform": platform.platform(),
        "accounting": m.snapshot(), "records": records,
        "unstarted_indices": [r["index"] for r in records if r["status"] == "unstarted"],
        "stopped_or_failed_indices": [r["index"] for r in records
                                       if r["status"] in ("stopped", "failed")],
        "summary": summarize(records), "verified_complete_improvement": "NONE"}
    write_json(ROOT / "results.json", result)
    print(json.dumps({k: result[k] for k in ("status", "first_failure", "elapsed_seconds",
          "accounting", "unstarted_indices", "stopped_or_failed_indices")}, sort_keys=True))
    return 0 if stop_reason is None else 2


if __name__ == "__main__":
    raise SystemExit(main())
