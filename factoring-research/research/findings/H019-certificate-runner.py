#!/usr/bin/env python3
"""Exclusive, single-shot H019 freeze/setup/controls/attempts/evidence runner.

Invoke ONCE under: timeout --signal=KILL 60s python -B THIS_FILE
No arithmetic candidate or reference code is imported before freeze.json exists.
"""
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import random
import signal
import subprocess
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
EVIDENCE = HERE / "H019-certificate-evidence"
CASES = [(4096, 15), (16384, 22), (65536, 34), (262144, 52)]
CONTROL_IDS = ["sqrt2-correct", "imaginary-correct", "zero-incorrect",
               "duplicate-disks", "repeated-polynomial"]


def raw_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def create_json(path, obj):
    with path.open("x", encoding="utf-8") as handle:
        json.dump(obj, handle, sort_keys=True, indent=2, allow_nan=False)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())


def replace_json(path, obj):
    temp = path.with_suffix(".pending")
    with temp.open("w", encoding="utf-8") as handle:
        json.dump(obj, handle, sort_keys=True, indent=2, allow_nan=False)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temp, path)


def last_event(path):
    last = None
    if path.exists():
        with path.open() as handle:
            for line in handle:
                try:
                    last = json.loads(line)
                except json.JSONDecodeError:
                    pass
    return last


class Deadline(Exception):
    pass


class Run:
    def __init__(self):
        self.start = time.monotonic()
        self.deadline = self.start+55
        self.active = None
        self.current = None
        self.out = {"schema": "H019-single-trial-v1", "controls": [
            {"id": v, "status": "unstarted"} for v in CONTROL_IDS],
            "research": [{"id": f"n{n}-d{d}", "n": n, "d": d, "status": "unstarted"}
                         for n, d in CASES], "complete": False}
        self.source_hashes = {}

    def event(self, event, **data):
        row = dict(event=event, elapsed_seconds=time.monotonic()-self.start, **data)
        with (EVIDENCE / "runner-events.jsonl").open("a") as handle:
            handle.write(json.dumps(row, sort_keys=True, allow_nan=False)+"\n")
            handle.flush()
            os.fsync(handle.fileno())

    def checkpoint(self):
        self.out["elapsed_seconds_at_checkpoint"] = time.monotonic()-self.start
        replace_json(EVIDENCE / "outcomes.json", self.out)

    def stop(self):
        if self.active is not None and self.active.poll() is None:
            os.killpg(self.active.pid, signal.SIGKILL)
            self.active.wait()

    def interrupted(self, signum, frame):
        self.stop()
        raise Deadline("internal55" if signum == signal.SIGALRM else "external_signal")

    def setup_and_freeze(self):
        setup = time.monotonic()
        inputs = []
        rng = random.Random(1919)
        for n, d in CASES:
            N = (1 << (n-1)) | rng.getrandbits(n-1) | 1
            assert N.bit_length() == n and N % 2 == 1
            name = f"n{n}-d{d}"
            payload = {"N_hex": hex(N)}
            path = EVIDENCE / (name+"-input.json")
            create_json(path, payload)
            inputs.append({"id": name, "n": n, "d": d, "N_hex": hex(N),
                           "N_only_input_sha256": raw_hash(path)})
        create_json(EVIDENCE / "inputs.json", {"seed": 1919, "cases": inputs})
        q = 2**40
        a = math.isqrt(2*q*q)
        if 8*q*q > (2*a+1)**2:
            a += 1
        controls = [
            {"id": "sqrt2-correct", "f": [-2, 0, 1], "disks": [[a, 0], [-a, 0]],
             "expected_accept": True, "expected_gate": "accepted"},
            {"id": "imaginary-correct", "f": [1, 0, 1], "disks": [[0, q], [0, -q]],
             "expected_accept": True, "expected_gate": "accepted"},
            {"id": "zero-incorrect", "f": [-2, 0, 1], "disks": [[0, 0], [-a, 0]],
             "expected_accept": False, "expected_gate": "disk_rouche"},
            {"id": "duplicate-disks", "f": [-2, 0, 1], "disks": [[a, 0], [a, 0]],
             "expected_accept": False, "expected_gate": "disjointness"},
            {"id": "repeated-polynomial", "f": [1, -2, 1], "disks": [[q, 0], [q, 0]],
             "expected_accept": False, "expected_gate": "squarefree"}]
        create_json(EVIDENCE / "controls.json", {"controls": controls})
        files = [HERE / ("H019-certificate-"+suffix) for suffix in
                 ("candidate.py", "reference.py", "runner.py", "protocol.json")]
        files += [ROOT / p for p in (
            "AGENTS.md", "README.md", "docs/SPECIFICATION.md", "RESEARCH_LOOP.md",
            "RESEARCH_TEAM.md", "research/STATE.md", "research/hypotheses/H019.md",
            "research/findings/H017-resultant-tail-supply.md",
            "research/findings/H017-independent-review.md")]
        frozen = EVIDENCE / "frozen"
        frozen.mkdir()
        mapping = []
        for path in files:
            data = path.read_bytes()
            destination = frozen / path.name
            with destination.open("xb") as handle:
                handle.write(data)
            sha = hashlib.sha256(data).hexdigest()
            self.source_hashes[str(path.relative_to(ROOT))] = sha
            mapping.append({"original": str(path.relative_to(ROOT)),
                            "snapshot": str(destination.relative_to(EVIDENCE)),
                            "bytes": len(data), "sha256": sha})
        input_files = [EVIDENCE / "inputs.json", EVIDENCE / "controls.json"]
        input_files += [EVIDENCE / (f"n{n}-d{d}-input.json") for n, d in CASES]
        manifest = {"schema": "H019-pre-execution-freeze-v1", "sources": mapping,
                    "inputs": [{"path": str(p.relative_to(EVIDENCE)), "sha256": raw_hash(p)}
                               for p in input_files],
                    "python": sys.version, "platform": platform.platform(),
                    "executable": sys.executable,
                    "execution_rule": "one wave,55 internal,60 external,3 controls,12 each research worker",
                    "input_and_freeze_seconds": time.monotonic()-setup,
                    "elapsed_before_freeze_write": time.monotonic()-self.start}
        create_json(EVIDENCE / "freeze.json", manifest)
        self.event("frozen_before_arithmetic_import", freeze_sha256=raw_hash(EVIDENCE / "freeze.json"))
        # First arithmetic-module import occurs only after the complete freeze.
        ref_path = frozen / "H019-certificate-reference.py"
        spec = importlib.util.spec_from_file_location("h019_prime_reference", ref_path)
        ref = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ref)
        create_json(EVIDENCE / "prime-certificate.json", ref.prime_certificate())
        self.out["setup_seconds"] = time.monotonic()-setup
        self.event("setup_complete", seconds=self.out["setup_seconds"])
        self.checkpoint()

    def attempt(self, name, path, limit):
        remaining = self.deadline-time.monotonic()-1.0
        if remaining <= 0:
            return {"status": "unstarted", "reason": "wave_budget"}
        cap = min(limit, remaining)
        prefix = EVIDENCE / name
        self.current = name
        self.event("worker_start", id=name, cap_seconds=cap)
        started = time.monotonic()
        timed_out = False
        command = [sys.executable, "-B", str(EVIDENCE / "frozen" / "H019-certificate-candidate.py"),
                   "--worker", str(path), str(prefix)]
        with (EVIDENCE / (name+"-stdout.log")).open("x") as stdout, \
                (EVIDENCE / (name+"-stderr.log")).open("x") as stderr:
            self.active = subprocess.Popen(command, stdout=stdout, stderr=stderr,
                                           cwd=ROOT, start_new_session=True)
            try:
                code = self.active.wait(timeout=max(0.0, cap-(time.monotonic()-started)))
            except subprocess.TimeoutExpired:
                timed_out = True
                self.stop()
                code = self.active.returncode
        self.active = None
        result_path = EVIDENCE / (name+"-result.json")
        if timed_out:
            result = {"status": "timeout", "reason": "killable_worker_cap"}
        elif result_path.exists():
            result = json.loads(result_path.read_text())
        else:
            result = {"status": "error", "reason": "worker_exited_without_result"}
        result.update(worker_wall_seconds=time.monotonic()-started, cap_seconds=cap,
                      exit_code=code, last_flushed_event=last_event(EVIDENCE / (name+"-events.jsonl")))
        if timed_out:
            result["partial_counters_only"] = True
            result["completed_result_file_exists"] = result_path.exists()
        self.event("worker_end", id=name, status=result["status"],
                   wall_seconds=result["worker_wall_seconds"])
        self.current = None
        return result

    def execute(self):
        self.setup_and_freeze()
        batch = self.attempt("controls", EVIDENCE / "controls.json", 3.0)
        self.out["control_batch"] = batch
        first_missing = True
        for row in self.out["controls"]:
            path = EVIDENCE / ("controls-"+row["id"]+"-result.json")
            if path.exists():
                row.update(json.loads(path.read_text()))
            elif first_missing:
                row.update(status=batch["status"] if batch["status"] != "pass" else "error",
                           reason="control_batch_incomplete")
                first_missing = False
        self.checkpoint()
        for row in self.out["research"]:
            row.update(self.attempt(row["id"], EVIDENCE / (row["id"]+"-input.json"), 12.0))
            self.checkpoint()

    def finalize(self):
        self.stop()
        if self.current and self.current != "controls":
            for row in self.out["research"]:
                if row["id"] == self.current:
                    row.update(status="timeout", reason="outer_deadline",
                               last_flushed_event=last_event(EVIDENCE / (self.current+"-events.jsonl")),
                               partial_counters_only=True)
        elif self.current == "controls":
            missing = True
            for row in self.out["controls"]:
                path = EVIDENCE / ("controls-"+row["id"]+"-result.json")
                if path.exists():
                    row.update(json.loads(path.read_text()))
                elif missing:
                    row.update(status="timeout", reason="outer_deadline")
                    missing = False
        statuses = ["pass", "unknown", "verification_failure", "error", "timeout", "unstarted"]
        self.out["research_tally"] = {s: sum(r["status"] == s for r in self.out["research"]) for s in statuses}
        self.out["control_tally"] = {s: sum(r["status"] == s for r in self.out["controls"]) for s in statuses}
        rejected = any(r["status"] == "verification_failure"
                       for r in self.out["controls"]+self.out["research"])
        continued = (all(r["status"] == "pass" for r in self.out["controls"]) and
                     all(r["status"] == "pass" for r in self.out["research"][-2:]))
        self.out["disposition"] = ("implementation_rejected" if rejected else
                                   "finite_continuation_pass" if continued else "inconclusive")
        self.out["verified_factoring_complexity_improvement"] = "NONE"
        self.out["complete"] = True
        self.out["original_sources_still_match"] = {
            path: raw_hash(ROOT / path) == sha for path, sha in self.source_hashes.items()}
        self.checkpoint()
        self.event("final_statuses_written", disposition=self.out["disposition"])
        files = sorted(p for p in EVIDENCE.rglob("*") if p.is_file())
        seal = {"files": [{"path": str(p.relative_to(EVIDENCE)), "bytes": p.stat().st_size,
                           "sha256": raw_hash(p)} for p in files],
                "elapsed_before_seal_write": time.monotonic()-self.start,
                "internal_budget_seconds": 55}
        create_json(EVIDENCE / "seal.json", seal)
        elapsed = time.monotonic()-self.start
        create_json(EVIDENCE / "completion.json", {
            "seal_sha256": raw_hash(EVIDENCE / "seal.json"),
            "elapsed_through_seal_seconds": elapsed,
            "within_55_seconds_through_seal": elapsed <= 55,
            "disposition": self.out["disposition"]})
        print(json.dumps({"evidence": str(EVIDENCE), "disposition": self.out["disposition"],
                          "controls": self.out["control_tally"], "research": self.out["research_tally"],
                          "elapsed_seconds": time.monotonic()-self.start}, sort_keys=True), flush=True)


def main():
    if EVIDENCE.exists():
        raise SystemExit("REFUSED: evidence directory already exists; no overwrite or second trial.")
    run = Run()
    EVIDENCE.mkdir()
    run.checkpoint()
    signal.signal(signal.SIGALRM, run.interrupted)
    signal.signal(signal.SIGTERM, run.interrupted)
    signal.setitimer(signal.ITIMER_REAL, max(0.001, run.deadline-time.monotonic()))
    try:
        run.execute()
    except Exception as error:
        run.out["outer_exception"] = {"type": type(error).__name__, "message": str(error),
                                      "traceback": traceback.format_exc()}
    finally:
        run.finalize()
        signal.setitimer(signal.ITIMER_REAL, 0)


if __name__ == "__main__":
    main()
