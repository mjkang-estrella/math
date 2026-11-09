#!/usr/bin/env python3
"""W011 frozen, one-run, standard-library ORACLE DIAGNOSTIC. Not a solver."""
from __future__ import annotations

import collections
import datetime
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import subprocess
import sys
import time
import traceback


BASE = Path(__file__).resolve().parent
PREFIX = "W011-basin-screen"


def path(suffix):
    return BASE / (PREFIX + suffix)


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def encode(value):
    return json.dumps(value, sort_keys=True, allow_nan=False)


def write_json(file, value):
    with file.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")
        stream.flush()
        os.fsync(stream.fileno())


def write_jsonl(file, rows):
    with file.open("x", encoding="utf-8") as stream:
        for row in rows:
            stream.write(encode(row) + "\n")
            stream.flush()
            os.fsync(stream.fileno())


def read_json(suffix):
    return json.loads(path(suffix).read_text())


def rational(numerator, denominator=1):
    f = Fraction(numerator, denominator)
    return {"numerator": f.numerator, "denominator": f.denominator,
            "decimal": float(f)}


class Deadline(Exception):
    pass


class Budget:
    def __init__(self, start, deadline):
        self.start = start
        self.deadline = deadline

    def check(self):
        if time.monotonic() >= self.deadline:
            raise Deadline("original 60-second diagnostic wall budget exhausted")


class Journal:
    def __init__(self, budget):
        self.budget = budget
        self.stream = path("-events.jsonl").open("a", encoding="utf-8")

    def emit(self, event, **data):
        row = {"event": event, "elapsed_wall_seconds": time.monotonic() - self.budget.start,
               **data}
        self.stream.write(encode(row) + "\n")
        self.stream.flush()
        os.fsync(self.stream.fileno())

    def close(self):
        self.stream.close()


def freeze():
    inputs = [path(".py"), path("-config.json"), path("-preregistration.md"),
              path("-execution-note.md")]
    inputs += sorted(BASE.glob(PREFIX + "-input-*"))
    manifest = {"frozen_utc": utc(), "algorithm": "sha256",
                "files": {p.name: {"sha256": digest(p), "bytes": p.stat().st_size}
                          for p in inputs},
                "python": sys.version, "executable": sys.executable,
                "platform": platform.platform(),
                "diagnostic_started": False}
    write_json(path("-freeze.json"), manifest)
    print(encode({"freeze": str(path("-freeze.json")), "files": len(inputs),
                  "source_sha256": digest(path(".py")),
                  "config_sha256": digest(path("-config.json"))}))


def verify_freeze():
    manifest = read_json("-freeze.json")
    for name, metadata in manifest["files"].items():
        if digest(BASE / name) != metadata["sha256"]:
            raise RuntimeError("Frozen input changed: " + name)
    return manifest


def scheduled(config):
    rows = []
    for b in config["field_bits"]:
        for seed in config["parameter_seeds"]:
            rows.append({"case_id": f"b{b}-seed{seed:02d}", "b": b,
                         "kind": "frozen_parameter", "seed": seed,
                         "rng_seed": 11000 + 100 * b + seed,
                         "depths": config["depths"], "status": "scheduled"})
        rows.append({"case_id": f"b{b}-cubic", "b": b, "kind": "cubic_control",
                     "seed": None, "rng_seed": None,
                     "depths": config["depths"], "status": "scheduled"})
    return rows


def first_prime(lower, budget):
    candidate = max(2, lower)
    while True:
        budget.check()
        prime = True
        for divisor in range(2, math.isqrt(candidate) + 1):
            if divisor % 128 == 0:
                budget.check()
            if candidate % divisor == 0:
                prime = False
                break
        if prime:
            return candidate
        candidate += 1


def map_value(t, modulus, beta):
    # The same beta is first computed modulo public N, then reduced locally.
    square = t * t % modulus
    return (t * (3 - square) * ((modulus + 1) // 2)
            + beta * t * ((1 - square) % modulus) ** 2) % modulus


def graph_census(modulus, beta, budget):
    """O(modulus) field table and reverse BFS: hidden-factor oracle diagnostic."""
    budget.check()
    graph = [0] * modulus
    reverse = [[] for _ in range(modulus)]
    for t in range(modulus):
        if t % 256 == 0:
            budget.check()
        value = map_value(t, modulus, beta)
        graph[t] = value
        reverse[value].append(t)
    if (graph[0], graph[1], graph[-1]) != (0, 1, modulus - 1):
        raise AssertionError("fixed targets/zero failed")
    for t in range(modulus):
        if t % 256 == 0:
            budget.check()
        if graph[-t % modulus] != -graph[t] % modulus:
            raise AssertionError("map oddness failed")

    def bfs(target):
        distance = [-1] * modulus
        distance[target] = 0
        queue = collections.deque([target])
        histogram = [1]
        visits = 0
        while queue:
            t = queue.popleft()
            visits += 1
            if visits % 256 == 0:
                budget.check()
            for predecessor in reverse[t]:
                if distance[predecessor] < 0:
                    d = distance[t] + 1
                    distance[predecessor] = d
                    if d == len(histogram):
                        histogram.append(0)
                    histogram[d] += 1
                    queue.append(predecessor)
        return histogram, distance

    positive, d_positive = bfs(1)
    negative, d_negative = bfs(modulus - 1)
    if positive != negative:
        raise AssertionError("two target first-hit histograms differ")
    if any(a >= 0 and b >= 0 for a, b in zip(d_positive, d_negative)):
        raise AssertionError("two fixed-target basins overlap")
    budget.check()
    total = [2 * count for count in positive]
    return {"modulus": modulus, "beta_local": beta % modulus,
            "plus_histogram": positive, "minus_histogram": negative,
            "combined_histogram": total, "target_histograms_equal": True,
            "map_oddness_checked": True, "fixed_points_checked": True,
            "basin_count": sum(total), "non_target_basin_count": sum(total) - 2,
            "never_hit_count": modulus - sum(total),
            "max_first_hit": len(total) - 1, "oracle_only": True}


def depth_metrics(p, q, hp_hist, hq_hist, depths, budget):
    """Exact counting forms of (3)-(6); no sampled walk approximation."""
    n = p * q
    hp = hq = simultaneous_equal = updates_numerator = 0
    wanted = set(depths)
    for k in range(max(depths) + 1):
        budget.check()
        if k:
            # Previous cumulative histograms, so this is survival through k-1.
            updates_numerator += (p - hp) * (q - hq)
        dp = hp_hist[k] if k < len(hp_hist) else 0
        dq = hq_hist[k] if k < len(hq_hist) else 0
        hp += dp
        hq += dq
        if (dp * dq) % 2:
            raise AssertionError("odd-symmetry simultaneous count not integral")
        simultaneous_equal += dp * dq // 2
        if k not in wanted:
            continue
        survival = (p - hp) * (q - hq)
        stop_success = n - survival - simultaneous_equal
        end_success = hp * q + hq * p - 3 * hp * hq // 2
        if not (0 <= end_success <= stop_success <= n):
            raise AssertionError("success count outside probability bounds")
        if stop_success + survival + simultaneous_equal != n:
            raise AssertionError("stopping statuses do not partition seeds")
        proxy = Fraction(n + updates_numerator, stop_success) if stop_success else None
        qualifies = (proxy is not None and
                     16 * proxy.numerator ** 2 <= p * proxy.denominator ** 2)
        yield {"k": k, "status": "completed", "h_p": rational(hp, p),
               "h_q": rational(hq, q), "h_p_count": hp, "h_q_count": hq,
               "S_end": rational(end_success, n),
               "S_stop": rational(stop_success, n),
               "stop_success_seed_count": stop_success,
               "stop_full_gcd_seed_count": simultaneous_equal,
               "stop_no_hit_seed_count": survival,
               "seed_count_denominator": n,
               "E_map_updates": rational(updates_numerator, n),
               "map_update_sum_over_seeds": updates_numerator,
               "one_plus_E_over_S": rational(proxy) if proxy is not None else None,
               "normalized_proxy": float(proxy) / math.sqrt(p) if proxy is not None else None,
               "zero_success": stop_success == 0,
               "undefined_proxy_reason": "zero_success" if stop_success == 0 else None,
               "qualifies_exactly": qualifies, "oracle_depth_choice": True,
               "optimistic_proxy_not_candidate_runtime": True}


def tiny_check():
    verify_freeze()
    config = read_json("-config.json")
    fixed = config["tiny_fixed_check"]
    p, q, a = fixed["p"], fixed["q"], fixed["a"]
    n = p * q
    beta = (a + 2) * pow(2 * a * (a + 1) ** 2, -1, n) % n
    start = time.monotonic()
    budget = Budget(start, start + 10)
    output = {"identity": fixed, "N": n, "beta_mod_N": beta,
              "source_sha256": digest(path(".py")), "started_utc": utc(),
              "role": "single fixed pre-main correctness instance, not screening"}
    try:
        locals_ = []
        for modulus in (p, q):
            census = graph_census(modulus, beta % modulus, budget)
            direct = {1: collections.Counter(), modulus - 1: collections.Counter()}
            for seed in range(modulus):
                t = seed
                seen = set()
                j = 0
                while t not in seen:
                    budget.check()
                    if t in direct:
                        direct[t][j] += 1
                        break
                    seen.add(t)
                    # Independent unexpanded expression, no graph lookup.
                    t = ((3*t - t**3) * pow(2, -1, modulus)
                         + beta*t*(1-t*t)**2) % modulus
                    j += 1
            for target, label in ((1, "plus_histogram"), (modulus-1, "minus_histogram")):
                direct_hist = [direct[target][j] for j in range(max(direct[target]) + 1)]
                assert direct_hist == census[label], (modulus, target, direct_hist, census)
            locals_.append(census)
        rows = list(depth_metrics(p, q, locals_[0]["combined_histogram"],
                                  locals_[1]["combined_histogram"], fixed["depths"], budget))
        for row in rows:
            success = full = nohit = updates = endpoint_success = 0
            for seed in range(n):
                t = seed
                outcome = "nohit"
                for j in range(row["k"] + 1):
                    budget.check()
                    stopped = False
                    for signed_target in (1, -1):
                        divisor = math.gcd(t - signed_target, n)
                        if 1 < divisor < n:
                            outcome, stopped = "success", True
                            break
                        if divisor == n:
                            outcome, stopped = "full", True
                            break
                    if stopped or j == row["k"]:
                        break
                    t = ((3*t-t**3)*pow(2, -1, n) + beta*t*(1-t*t)**2) % n
                    updates += 1
                success += outcome == "success"
                full += outcome == "full"
                nohit += outcome == "nohit"
                t = seed
                for _ in range(row["k"]):
                    budget.check()
                    t = ((3*t-t**3)*pow(2, -1, n) + beta*t*(1-t*t)**2) % n
                endpoint_success += any(1 < math.gcd(t-z, n) < n for z in (1, -1))
            assert success == row["stop_success_seed_count"], row
            assert full == row["stop_full_gcd_seed_count"], row
            assert nohit == row["stop_no_hit_seed_count"], row
            assert updates == row["map_update_sum_over_seeds"], row
            assert rational(endpoint_success, n) == row["S_end"], row
            row["direct_counts"] = {"success": success, "full_gcd": full,
                                    "no_hit": nohit, "updates": updates,
                                    "endpoint_success": endpoint_success}
        output.update(status="passed", local_censuses=locals_, depths=rows)
    except Exception:
        output.update(status="failed", traceback=traceback.format_exc())
    output["elapsed_seconds"] = time.monotonic() - start
    write_json(path("-tiny-check.json"), output)
    print(encode({"tiny_check": output["status"], "identity": fixed}))
    if output["status"] != "passed":
        raise SystemExit(1)


def worker():
    config = read_json("-config.json")
    run = read_json("-run.json")
    budget = Budget(run["start_monotonic"], run["deadline_monotonic"])
    log = Journal(budget)
    rows = scheduled(config)
    active = None
    try:
        for b in config["field_bits"]:
            budget.check()
            log.emit("pair_setup_started", b=b)
            p = first_prime(2 ** b, budget)
            q = first_prime(p + 1, budget)
            n = p * q
            log.emit("pair_ready", b=b, p=p, q=q, N=n, gcd_two=math.gcd(2, n),
                     hidden_factors_role="oracle diagnostic only")
            for spec in (r for r in rows if r["b"] == b):
                budget.check()
                active = spec["case_id"]
                log.emit("case_started", case_id=active, b=b, p=p, q=q, N=n)
                try:
                    if spec["kind"] == "frozen_parameter":
                        budget.check()
                        a = random.Random(spec["rng_seed"]).randrange(n)
                        log.emit("parameter_draw", case_id=active, a=a,
                                 rng_seed=spec["rng_seed"], randrange_calls=1,
                                 sampler_inputs="N and registered RNG seed only")
                        saw_full = False
                        factor = None
                        for label, value in (("a", a), ("a-1", a-1), ("a+1", a+1)):
                            budget.check()
                            divisor = math.gcd(value, n)
                            log.emit("chart_gcd", case_id=active, expression=label,
                                     value=value, gcd=divisor,
                                     outcome=("proper_factor" if 1 < divisor < n else
                                              "full_gcd" if divisor == n else "unit"))
                            saw_full |= divisor == n
                            if 1 < divisor < n:
                                factor = divisor
                                break
                        if factor is not None:
                            log.emit("case_terminal", case_id=active, status="chart_success",
                                     factor=factor, factor_verified=(n % factor == 0),
                                     full_gcd_seen=saw_full, qualifies=False)
                            active = None
                            continue
                        if saw_full:
                            log.emit("case_terminal", case_id=active,
                                     status="chart_full_failure", qualifies=False)
                            active = None
                            continue
                        budget.check()
                        denominator = 2 * a * (a+1) ** 2 % n
                        beta = (a+2) * pow(denominator, -1, n) % n
                        log.emit("chart_clean", case_id=active, denominator_mod_N=denominator,
                                 beta_mod_N=beta, a_equals_minus_two=(a == n-2))
                    else:
                        beta = 0
                        log.emit("control_map", case_id=active, beta_mod_N=0,
                                 map="C(T)=(3T-T^3)/2", parameter_draws=0)
                    hp = graph_census(p, beta % p, budget)
                    log.emit("local_census", case_id=active, field="p", **hp)
                    hq = graph_census(q, beta % q, budget)
                    log.emit("local_census", case_id=active, field="q", **hq)
                    metrics = []
                    for metric in depth_metrics(p, q, hp["combined_histogram"],
                                                hq["combined_histogram"], config["depths"], budget):
                        log.emit("depth_completed", case_id=active, **metric)
                        metrics.append(metric)
                    budget.check()
                    finite = [r for r in metrics if not r["zero_success"]]
                    best = min(finite, key=lambda r: (Fraction(r["one_plus_E_over_S"]["numerator"],
                                                             r["one_plus_E_over_S"]["denominator"]),
                                                       r["k"])) if finite else None
                    log.emit("case_terminal", case_id=active,
                             status="clean_completed" if spec["kind"] == "frozen_parameter"
                                    else "control_completed",
                             best_k=best["k"] if best else None,
                             best_normalized_proxy=best["normalized_proxy"] if best else None,
                             qualifies=any(r["qualifies_exactly"] for r in metrics),
                             depths_completed=len(metrics))
                    active = None
                except Deadline:
                    raise
                except Exception:
                    log.emit("case_terminal", case_id=active, status="failed",
                             traceback=traceback.format_exc(), qualifies=False)
                    active = None
        log.emit("worker_terminal", status="completed")
    except Deadline:
        if active:
            log.emit("case_terminal", case_id=active, status="timed_out", qualifies=False)
        log.emit("worker_terminal", status="deadline", active_case=active)
    except Exception:
        log.emit("worker_terminal", status="failed", active_case=active,
                 traceback=traceback.format_exc())
        raise
    finally:
        log.close()


def main_run():
    verify_freeze()
    if read_json("-tiny-check.json")["status"] != "passed":
        raise RuntimeError("The fixed pre-main correctness check did not pass")
    config = read_json("-config.json")
    # Exclusive run marker prevents main retries even if setup or process launch fails.
    start = time.monotonic()
    deadline = start + config["wall_seconds"]
    run = {"started_utc": utc(), "start_monotonic": start,
           "deadline_monotonic": deadline, "wall_cap_seconds": config["wall_seconds"],
           "source_sha256": digest(path(".py")),
           "config_sha256": digest(path("-config.json")),
           "freeze_sha256": digest(path("-freeze.json")),
           "main_run_number": 1, "python": sys.version,
           "clock_scope": "includes schedule persistence, process startup, prime/parameter setup and oracle diagnostic"}
    write_json(path("-run.json"), run)
    supervisor = {"outer_timeout_used": True, "hard_timeout": False,
                  "worker_returncode": None, "worker_launch_attempts": 0}
    proc = None
    try:
        write_jsonl(path("-scheduled.jsonl"), scheduled(config))
        with path("-events.jsonl").open("x"):
            pass
        with path("-worker.log").open("x", encoding="utf-8") as logfile:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                supervisor["status"] = "deadline_before_worker"
            else:
                supervisor["worker_launch_attempts"] = 1
                proc = subprocess.Popen([sys.executable, "-B", str(path(".py")), "worker"],
                                        stdout=logfile, stderr=subprocess.STDOUT,
                                        cwd=BASE.parent.parent, close_fds=True)
                supervisor["worker_pid"] = proc.pid
                try:
                    supervisor["worker_returncode"] = proc.wait(timeout=max(0, deadline-time.monotonic()))
                    supervisor["status"] = "worker_exited"
                except subprocess.TimeoutExpired:
                    supervisor["hard_timeout"] = True
                    supervisor["kill_elapsed_seconds"] = time.monotonic() - start
                    proc.kill()
                    try:
                        supervisor["worker_returncode"] = proc.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        supervisor["reap_timeout"] = True
                    supervisor["status"] = "hard_timeout"
    except Exception:
        supervisor.update(status="supervisor_error", traceback=traceback.format_exc())
        if proc is not None and proc.poll() is None:
            proc.kill()
            try:
                supervisor["worker_returncode"] = proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                supervisor["reap_timeout"] = True
    finally:
        supervisor["elapsed_through_worker_exit_seconds"] = time.monotonic() - start
        supervisor["finished_utc"] = utc()
        write_json(path("-supervisor.json"), supervisor)
    # Only retained-data aggregation below. Never a diagnostic continuation.
    summarize()


def retained_events():
    file = path("-events.jsonl")
    if not file.exists():
        return [], [{"reason": "journal_not_created"}]
    events, malformed = [], []
    for number, line in enumerate(file.read_text().splitlines(), 1):
        try:
            events.append(json.loads(line))
        except json.JSONDecodeError:
            malformed.append({"line": number, "reason": "incomplete_or_malformed_preserved_raw"})
    return events, malformed


def status_counts(rows, key="status", depth=False):
    names = (["completed", "not_applicable_chart", "failed", "failed_interrupted",
              "timed_out", "unstarted"] if depth else
             ["clean_completed", "chart_success", "chart_full_failure", "control_completed",
              "failed", "failed_interrupted", "timed_out", "unstarted"])
    counts = {name: 0 for name in names}
    counts.update(collections.Counter(row[key] for row in rows))
    return counts


def summarize():
    config = read_json("-config.json")
    verify_freeze()
    events, malformed = retained_events()
    supervisor = read_json("-supervisor.json")
    worker_terminal = next((e for e in reversed(events) if e["event"] == "worker_terminal"), {})
    deadline = supervisor["hard_timeout"] or worker_terminal.get("status") == "deadline" or \
        supervisor.get("status") == "deadline_before_worker"
    bycase = collections.defaultdict(list)
    pairs = {}
    for event in events:
        if "case_id" in event:
            bycase[event["case_id"]].append(event)
        if event["event"] == "pair_ready":
            pairs[event["b"]] = event
    cases, depths = [], []
    for spec in scheduled(config):
        history = bycase[spec["case_id"]]
        row = {**spec, "p": None, "q": None, "N": None, "a": None,
               "beta_mod_N": None, "chart_gcds": [], "local_censuses": {},
               "qualifies": False, "completed_depths": []}
        if spec["b"] in pairs:
            row.update({k: pairs[spec["b"]][k] for k in ("p", "q", "N")})
        terminal = None
        metrics = {}
        for event in history:
            kind = event["event"]
            if kind == "parameter_draw":
                row["a"] = event["a"]
                row["randrange_calls"] = event["randrange_calls"]
            elif kind == "chart_gcd":
                row["chart_gcds"].append(event)
            elif kind in ("chart_clean", "control_map"):
                row["beta_mod_N"] = event["beta_mod_N"]
                row["clean_chart"] = kind == "chart_clean"
            elif kind == "local_census":
                row["local_censuses"][event["field"]] = event
            elif kind == "depth_completed":
                metrics[event["k"]] = event
            elif kind == "case_terminal":
                terminal = event
        if terminal:
            row.update({k: v for k, v in terminal.items() if k not in ("event", "case_id")})
        elif any(e["event"] == "case_started" for e in history):
            row["status"] = "timed_out" if deadline else "failed_interrupted"
            row["status_reason"] = "No durable terminal event; see supervisor and raw journal"
        else:
            row["status"] = "unstarted"
            row["status_reason"] = "deadline" if deadline else "worker_or_setup_failure"
        row["completed_depths"] = sorted(metrics)
        row["counts_toward_primary_eight"] = (spec["kind"] == "frozen_parameter" and
                                                row["status"] == "clean_completed" and
                                                row["qualifies"])
        row["oracle_only"] = True
        cases.append(row)
        for k in config["depths"]:
            depth = {"case_id": spec["case_id"], "b": spec["b"], "seed": spec["seed"],
                     "kind": spec["kind"], "p": row["p"], "q": row["q"], "N": row["N"],
                     "a": row["a"], "k": k, "case_status": row["status"]}
            if k in metrics:
                depth.update(metrics[k])
            else:
                depth.update(status=("not_applicable_chart" if row["status"] in
                                      ("chart_success", "chart_full_failure") else row["status"]),
                             reason=row["status"], S_stop=None, E_map_updates=None,
                             normalized_proxy=None, qualifies_exactly=False,
                             missing_is_not_zero=True)
            depths.append(depth)
    write_jsonl(path("-cases.jsonl"), cases)
    write_jsonl(path("-depths.jsonl"), depths)
    pair_summaries = []
    primary_complete = True
    for b in config["field_bits"]:
        parameter_cases = [r for r in cases if r["b"] == b and r["kind"] == "frozen_parameter"]
        controls = [r for r in cases if r["b"] == b and r["kind"] == "cubic_control"]
        clean = [r for r in parameter_cases if r["status"] == "clean_completed"]
        complete = all(r["status"] in ("clean_completed", "chart_success", "chart_full_failure")
                       for r in parameter_cases)
        qualifiers = sum(r["counts_toward_primary_eight"] for r in parameter_cases)
        item = {"b": b, "p": pairs.get(b, {}).get("p"), "q": pairs.get(b, {}).get("q"),
                "N": pairs.get(b, {}).get("N"), "scheduled_parameters": len(parameter_cases),
                "status_counts": status_counts(parameter_cases),
                "qualifying_clean": qualifiers,
                "qualifying_case_ids": [r["case_id"] for r in parameter_cases if r["counts_toward_primary_eight"]],
                "primary": b in config["primary_bits"], "parameter_pair_complete": complete,
                "best_normalized_proxy_among_clean": min((r["best_normalized_proxy"] for r in clean
                                                           if r["best_normalized_proxy"] is not None), default=None),
                "control_status": controls[0]["status"],
                "control_best_k": controls[0].get("best_k"),
                "control_best_normalized_proxy": controls[0].get("best_normalized_proxy")}
        pair_summaries.append(item)
        if item["primary"] and not complete:
            primary_complete = False
    if not primary_complete or malformed:
        disposition = "INCONCLUSIVE"
    elif all(r["qualifying_clean"] >= config["minimum_qualifying_clean"]
             for r in pair_summaries if r["primary"]):
        disposition = "PASS_PILOT_ONLY"
    else:
        disposition = "REJECTED"
    summary = {"disposition": disposition, "verified_improvement": "NONE",
               "primary_pairs_completely_accounted": primary_complete,
               "cases_scheduled": len(cases), "depth_slots_scheduled": len(depths),
               "case_status_counts": status_counts(cases),
               "depth_status_counts": status_counts(depths, depth=True),
               "zero_success_completed_depths": sum(r.get("zero_success", False) for r in depths),
               "pair_summaries": pair_summaries, "supervisor": supervisor,
               "worker_terminal": worker_terminal, "malformed_journal_lines": malformed,
               "source_sha256": digest(path(".py")),
               "config_sha256": digest(path("-config.json")),
               "freeze_sha256": digest(path("-freeze.json")),
               "main_run_count": 1, "oracle_only": True}
    write_json(path("-summary.json"), summary)
    report(summary, cases)
    manifest = {"created_utc": utc(), "disposition": disposition,
                "self_excluded_to_avoid_hash_cycle": path("-manifest.json").name,
                "files": {p.name: {"sha256": digest(p), "bytes": p.stat().st_size}
                          for p in sorted(BASE.glob(PREFIX + "*"))
                          if p.is_file() and p != path("-manifest.json")}}
    write_json(path("-manifest.json"), manifest)
    print(encode({"disposition": disposition, "cases": summary["case_status_counts"],
                  "depths": summary["depth_status_counts"],
                  "elapsed_seconds": supervisor["elapsed_through_worker_exit_seconds"],
                  "primary": [p for p in pair_summaries if p["primary"]]}))


def report(summary, cases):
    text = ["# W011 frozen-basin diagnostic\n",
            f"Disposition: **{summary['disposition']}** for the preregistered window. "
            "Verified factoring improvement: **NONE**.\n",
            "The exact finite-field census is an oracle diagnostic. The map coefficient "
            "was acquired from the single prescribed N-only parameter draw; hidden p,q "
            "were used only to analyze its local functional graphs. No candidate factoring "
            "runtime was measured or implemented.\n",
            f"One main run; total wall through worker exit: "
            f"{summary['supervisor']['elapsed_through_worker_exit_seconds']:.6f} seconds "
            "within the registered 60-second cap unless the supervisor records a deadline. "
            "Prime setup, parameter draws, chart gcds, tables, BFS, all depths and durable "
            "journal writes are charged. Source/config were frozen before the one fixed "
            "p=5,q=7,a=2 check, which passed exact direct-orbit and all-CRT-seed checks "
            "of endpoint/stopping probabilities and map-update expectations.\n",
            "Primary criterion: at least 8 of the original 16 records on each of b=13 "
            "and b=15 must be clean and have min_k (1+E)/(S_stop*sqrt(p)) <= 1/4. "
            "Chart successes do not qualify. Missing primary analysis is inconclusive.\n"]
    for pair in summary["pair_summaries"]:
        text.append(f"- b={pair['b']}: p={pair['p']}, q={pair['q']}; statuses "
                    f"{encode(pair['status_counts'])}; qualifying clean "
                    f"{pair['qualifying_clean']}/16; best clean normalized proxy "
                    f"{pair['best_normalized_proxy_among_clean']}; cubic control "
                    f"{pair['control_status']}, best normalized proxy "
                    f"{pair['control_best_normalized_proxy']} at k={pair['control_best_k']}.")
    text += ["", f"All case statuses: {encode(summary['case_status_counts'])}. "
             f"All {summary['depth_slots_scheduled']} depth slots: "
             f"{encode(summary['depth_status_counts'])}. Zero-success completed depths: "
             f"{summary['zero_success_completed_depths']}. Every case and every fixed depth "
             "is retained; no seeds or adverse basins are omitted.\n",
             "The optimistic work proxy omits gcds, inversion/setup constants, random bits "
             "and bit costs. Best depth uses hidden-factor oracle histograms and is not "
             "an N-only schedule. Cubic C is one fixed-map control per pair, not Pollard rho. "
             "No fitted exponent, monotone trend, asymptotic bound, ECM/GNFS comparison "
             "or speedup claim follows. Full-gcd stopping failures and no-hit survival "
             "are included in every exact S_stop count.\n"]
    if summary["disposition"] == "REJECTED":
        text.append("The registered supply of sufficiently cheap useful basins fails in "
                    "this finite window. This rejects this pilot, not every parameter of "
                    "the family or factoring in general. Reopening this branch would need "
                    "a new justified mechanism or theorem for N-only useful-parameter "
                    "supply and hitting cost, followed by separately authorized independent "
                    "validation; increasing this run or selecting favorable seeds is not "
                    "part of this delivery.\n")
    elif summary["disposition"] == "PASS_PILOT_ONLY":
        text.append("Passing licenses independent validation and development of an N-only "
                    "depth schedule, with full setup/extraction costs. It establishes no "
                    "factoring speedup. No additional run is authorized here.\n")
    else:
        text.append("Incomplete analysis prevents application of the primary criterion. "
                    "Missing or interrupted work is censored, not zero cost or a fabricated "
                    "failure. No continuation or replacement run was performed.\n")
    text += ["The separate mathematical review is not duplicated here; this finite check "
             "does not prove identities (1)-(5), basin growth, or a complexity theorem. "
             "No shared solver, Lean, state, package, commit or publication changes. The "
             "shared check.sh was not run because it launches additional tests/builds and "
             "writes outside the assigned prefix; the user's bounded-check scope controls.\n",
             f"Source SHA-256: `{summary['source_sha256']}`.\n",
             f"Config SHA-256: `{summary['config_sha256']}`.\n",
             f"Freeze manifest SHA-256: `{summary['freeze_sha256']}`.\n",
             "Delivery: `-preregistration.md`, `-execution-note.md`, `.py`, `-config.json`, "
             "`-freeze.json`, `-tiny-check.json`, `-run.json`, `-scheduled.jsonl`, "
             "`-events.jsonl` (durable raw chronology and full histograms), `-cases.jsonl` "
             "(all per-case statuses), `-depths.jsonl` (all ten depths for every case), "
             "`-supervisor.json`, `-worker.log`, `-summary.json`, this report and "
             "`-manifest.json`, plus the frozen instruction snapshots. All share the "
             "`W011-basin-screen` prefix. The manifest hashes every artifact except itself.\n"]
    with path("-report.md").open("x", encoding="utf-8") as stream:
        stream.write("\n".join(text))
        stream.flush()
        os.fsync(stream.fileno())


def verify_delivery():
    verify_freeze()
    manifest = read_json("-manifest.json")
    for name, record in manifest["files"].items():
        if digest(BASE / name) != record["sha256"]:
            raise RuntimeError("Delivery hash mismatch: " + name)
    config = read_json("-config.json")
    expected = scheduled(config)
    cases = [json.loads(line) for line in path("-cases.jsonl").read_text().splitlines()]
    depths = [json.loads(line) for line in path("-depths.jsonl").read_text().splitlines()]
    assert [r["case_id"] for r in cases] == [r["case_id"] for r in expected]
    assert [(r["case_id"], r["k"]) for r in depths] == [
        (r["case_id"], k) for r in expected for k in config["depths"]]
    for row in cases:
        if row["status"] in ("clean_completed", "control_completed"):
            assert row["completed_depths"] == config["depths"]
            assert set(row["local_censuses"]) == {"p", "q"}
            for field, census in row["local_censuses"].items():
                assert census["plus_histogram"] == census["minus_histogram"]
                assert sum(census["combined_histogram"]) + census["never_hit_count"] == row[field]
        if row["counts_toward_primary_eight"]:
            assert row["kind"] == "frozen_parameter" and row["status"] == "clean_completed"
        if row["a"] is not None:
            assert row["randrange_calls"] == 1
    assert status_counts(cases) == read_json("-summary.json")["case_status_counts"]
    assert status_counts(depths, depth=True) == read_json("-summary.json")["depth_status_counts"]
    print(encode({"delivery_hashes_verified": len(manifest["files"]),
                  "frozen_hashes_verified": len(read_json("-freeze.json")["files"]),
                  "case_slots_verified": len(cases), "depth_slots_verified": len(depths),
                  "disposition": manifest["disposition"]}))


if __name__ == "__main__":
    commands = {"freeze": freeze, "tiny-check": tiny_check, "run": main_run,
                "worker": worker, "summarize": summarize, "verify": verify_delivery}
    if len(sys.argv) != 2 or sys.argv[1] not in commands:
        raise SystemExit("Usage: W011-basin-screen.py freeze|tiny-check|run|worker|summarize|verify")
    commands[sys.argv[1]]()
