"""One-shot W006 evaluator/supervisor; standard library only. No reruns."""
import time
PROCESS_START = time.perf_counter()
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import tracemalloc

BASE = Path(__file__).resolve().parent
PREFIX = "W006-coefficient-validation-"
INPUTS = [77, 143, 221, 437, 899, 1763, 2701, 3599, 49, 121, 97, 127]
DEGREES = [2, 4, 8, 16]
# Evaluator-only ground truth. The candidate is a separate module with N,L input.
FACTORS = {77: (7, 11), 143: (11, 13), 221: (13, 17), 437: (19, 23),
           899: (29, 31), 1763: (41, 43), 2701: (37, 73), 3599: (59, 61)}
MIB = 1024 * 1024


def emit(kind, data):
    print(json.dumps({"kind": kind, "data": data}, separators=(",", ":")), flush=True)


def attempt(N, L):
    tracemalloc.start()
    deadline = PROCESS_START + 1.0

    def check():
        if time.perf_counter() >= deadline:
            raise TimeoutError("attempt_time_including_controls")
        if tracemalloc.get_traced_memory()[1] > 32 * MIB:
            raise MemoryError("soft_traced_allocation")

    result = {"N": N, "L": L, "status": "UNKNOWN", "factor": None,
              "candidate": None, "control": {}, "stop_reason": "unstarted"}
    try:
        check()
        spec = importlib.util.spec_from_file_location(
            "frozen_w006_candidate", BASE / (PREFIX + "candidate.py"))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        result["candidate"] = module.candidate(N, L)
        check()
        t = time.perf_counter()
        n, m = N - 1, (N - 1) // 2
        central = math.comb(n, m)
        central_gcd = math.gcd(central, N)
        control = result["control"]
        control.update({"central_bits": central.bit_length(),
                        "central_mod_N": central % N,
                        "central_gcd": central_gcd,
                        "central_seconds": time.perf_counter() - t,
                        "expected_A1_factor": FACTORS.get(N, (None,))[0],
                        "A1_match": central_gcd == FACTORS[N][0] if N in FACTORS else None})
        emit("central_control", control)
        check()
        t = time.perf_counter()
        row = 1
        folded = [0] * L
        aliases = []
        max_bits = 1
        max_temp_bits = 1
        row_central = None
        for k in range(n + 1):
            check()
            folded[k % L] = (folded[k % L] + row) % N
            max_bits = max(max_bits, row.bit_length())
            if k == m:
                row_central = row
            elif k % L == m % L:
                aliases.append([k, row % N])
            if k < n:
                product = row * (n - k)
                max_temp_bits = max(max_temp_bits, product.bit_length())
                row, rem = divmod(product, k + 1)
                if rem:
                    raise ArithmeticError("inexact row recurrence")
        control.update({"row_seconds": time.perf_counter() - t,
                        "row_coefficients_computed": n + 1,
                        "row_recurrence_steps": n,
                        "row_max_coefficient_bits": max_bits,
                        "row_max_product_bits": max_temp_bits,
                        "row_central_equals_comb": row_central == central,
                        "folded_vector": folded,
                        "vector_match": folded == result["candidate"]["residues"],
                        "central_index": m, "central_class": m % L,
                        "central_aliases_index_residue_mod_N": aliases,
                        "central_alias_sum_mod_N": (folded[m % L] - central) % N})
        emit("row_control", control)
        check()
        c = result["candidate"]
        invalid = c["factor"] is not None and not (1 < c["factor"] < N and N % c["factor"] == 0)
        mismatch = (c["residues"] is not None and not control["vector_match"])
        if invalid or mismatch or not control["row_central_equals_comb"] or control["A1_match"] is False:
            result["stop_reason"] = "implementation_rejected"
            result["implementation_rejected"] = True
        else:
            result["status"] = c["status"]
            result["factor"] = c["factor"]
            result["stop_reason"] = c["stop_reason"]
    except Exception as exc:
        result["status"] = "UNKNOWN"
        result["factor"] = None
        result["stop_reason"] = "attempt_exception: " + repr(exc)
    result["worker_seconds_including_setup_controls"] = time.perf_counter() - PROCESS_START
    result["traced_current_bytes"], result["traced_peak_bytes"] = tracemalloc.get_traced_memory()
    emit("attempt", result)


def supervisor():
    marker = BASE / (PREFIX + "execution-started.json")
    with marker.open("x") as f:
        json.dump({"started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                   "pid": os.getpid(), "single_execution": True}, f)
    records = [{"N": n, "L": l, "status": "UNKNOWN", "factor": None,
                "stop_reason": "unstarted", "cold_seconds": None}
               for n in INPUTS for l in DEGREES]
    output = BASE / (PREFIX + "outcomes.json")
    if output.exists():
        raise RuntimeError("refusing to overwrite prior outcomes")
    total_bytes = 0
    total_peak = 0
    whole_reason = "completed"

    def save():
        doc = {"inputs": INPUTS, "degrees": DEGREES, "attempts": records,
               "whole_seconds": time.perf_counter() - PROCESS_START,
               "whole_stop_reason": whole_reason,
               "worker_evidence_bytes": total_bytes,
               "supervisor_traced_peak_bytes": total_peak}
        raw = json.dumps(doc, indent=2).encode()
        if len(raw) + total_bytes > 16 * MIB:
            raise RuntimeError("total_evidence_limit")
        output.write_bytes(raw)

    tracemalloc.start()
    save()
    manifest = json.loads((BASE / (PREFIX + "freeze.json")).read_text())
    for name, expected in manifest["sha256"].items():
        if hashlib.sha256((BASE / name).read_bytes()).hexdigest() != expected:
            whole_reason = "frozen_hash_mismatch"
            for r in records:
                r["stop_reason"] = "unstarted_frozen_hash_mismatch"
            save()
            return
    for index, initial in enumerate(records):
        remaining = 60.0 - (time.perf_counter() - PROCESS_START)
        if remaining <= 0 or total_bytes >= 15 * MIB or total_peak > 32 * MIB:
            whole_reason = "whole_cap"
            for r in records[index:]:
                r["stop_reason"] = "unstarted_whole_cap"
            break
        initial["stop_reason"] = "started_no_terminal_record"
        save()
        n, l = initial["N"], initial["L"]
        started = time.perf_counter()
        raw = b""
        stderr = b""
        try:
            proc = subprocess.run([sys.executable, "-B", str(Path(__file__).resolve()),
                                   "--attempt", str(n), str(l)],
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  timeout=min(1.0, remaining), check=False)
            raw, stderr = proc.stdout, proc.stderr
            initial["worker_exit_code"] = proc.returncode
        except subprocess.TimeoutExpired as exc:
            raw, stderr = exc.stdout or b"", exc.stderr or b""
            initial["stop_reason"] = "hard_attempt_timeout"
        except Exception as exc:
            initial["stop_reason"] = "launch_exception: " + repr(exc)
        initial["cold_seconds"] = time.perf_counter() - started
        if len(raw) + len(stderr) > MIB:
            raw, stderr = raw[:MIB - min(len(stderr), 4096)], stderr[:4096]
            initial["stop_reason"] = "attempt_evidence_cap_truncated"
        name = PREFIX + f"attempt-{index + 1:02d}-{n}-{l}.jsonl"
        (BASE / name).write_bytes(raw)
        total_bytes += len(raw) + len(stderr)
        initial["events_file"] = name
        initial["stderr"] = stderr.decode(errors="replace")
        initial["evidence_bytes"] = len(raw) + len(stderr)
        if initial["stop_reason"] == "started_no_terminal_record":
            try:
                events = [json.loads(line) for line in raw.splitlines()]
                terminals = [e["data"] for e in events if e["kind"] == "attempt"]
                if len(terminals) != 1 or initial["worker_exit_code"] != 0:
                    raise ValueError("missing/duplicate terminal or nonzero exit")
                records[index] = {**initial, **terminals[0]}
            except Exception as exc:
                initial["stop_reason"] = "evidence_parse_exception: " + repr(exc)
        total_peak = max(total_peak, tracemalloc.get_traced_memory()[1])
        save()
    save()
    print(json.dumps({"attempts": len(records), "whole_stop_reason": whole_reason,
                      "whole_seconds": time.perf_counter() - PROCESS_START}))


if __name__ == "__main__":
    if len(sys.argv) == 4 and sys.argv[1] == "--attempt":
        attempt(int(sys.argv[2]), int(sys.argv[3]))
    elif len(sys.argv) == 1:
        supervisor()
    else:
        raise SystemExit("invalid invocation")
