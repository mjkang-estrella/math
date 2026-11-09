import hashlib
import json
import math
import platform
import re
import statistics
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

from .algorithms import ALGORITHMS
from .core import valid_factor
from .corpus import FAMILIES, generate

ROOT = Path(__file__).resolve().parents[1]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_config(c: dict) -> None:
    if c.get("schema") != 1:
        raise ValueError("unsupported config schema")
    for name in ("bits", "families", "algorithm_seeds", "algorithms"):
        if not isinstance(c.get(name), list) or not c[name] or len(set(c[name])) != len(c[name]):
            raise ValueError(f"{name} must be a nonempty list without duplicates")
    if any(type(b) is not int or not 12 <= b <= 40 for b in c["bits"]):
        raise ValueError("bits must be integers in [12, 40]")
    if not set(c["families"]) <= set(FAMILIES):
        raise ValueError("unknown input family")
    if "unbalanced" in c["families"] and max(c["bits"]) > 28:
        raise ValueError("unbalanced corpus supports at most 28 bits")
    if not set(c["algorithms"]) <= set(ALGORITHMS):
        raise ValueError("unknown algorithm; register it in algorithms.py")
    for name in ("samples_per_family", "max_events", "max_operand_bits"):
        if type(c.get(name)) is not int or c[name] <= 0:
            raise ValueError(f"{name} must be a positive integer")
    if type(c.get("corpus_seed")) is not int or any(type(s) is not int for s in c["algorithm_seeds"]):
        raise ValueError("seeds must be integers")
    if type(c.get("include_controls", True)) is not bool:
        raise ValueError("include_controls must be boolean")
    for name in ("timeout_seconds", "total_seconds"):
        value = c.get(name)
        if type(value) not in (int, float) or not math.isfinite(value) or not 0 < value <= 60:
            raise ValueError(f"{name} must be finite, positive, and <= 60")
    count = len(c["bits"]) * len(c["families"]) * c["samples_per_family"]
    if count * len(c["algorithms"]) * len(c["algorithm_seeds"]) > 10_000:
        raise ValueError("bounded wave permits at most 10,000 non-control trials")


def run_one(algorithm: str, n: int, seed: int, c: dict, timeout: float) -> dict:
    request = {"algorithm": algorithm, "n": n, "seed": seed,
               "max_events": c["max_events"], "max_operand_bits": c["max_operand_bits"]}
    start = time.perf_counter()
    try:
        p = subprocess.run([sys.executable, "-m", "factoring_lab.worker"],
                           input=json.dumps(request), capture_output=True, text=True,
                           cwd=ROOT, timeout=timeout, check=False)
        if p.returncode:
            result = {"status": "error", "detail": p.stderr[-2000:]}
        else:
            result = json.loads(p.stdout)
            # Parent verifies success independently, outside candidate runtime.
            if result.get("status") == "success" and not valid_factor(n, result.get("factor")):
                result["status"] = "invalid"
    except subprocess.TimeoutExpired:
        result = {"status": "timeout", "detail": "subprocess killed; event counters unavailable"}
    except (ValueError, OSError) as exc:
        result = {"status": "error", "detail": str(exc)}
    return {**result, "process_seconds": time.perf_counter() - start}


def summary_text(rows: list[dict]) -> str:
    grouped = defaultdict(list)
    for row in rows:
        grouped[(row["family"], row["bits"], row["algorithm"])].append(row)
    out = ["# Bounded experiment report", "",
           "Descriptive measurements only. No polynomial-time or novelty conclusion.",
           "Each trial is one (instance, algorithm seed); repeats are not independent instances.",
           "Event medians use successes only and are selection-biased if any trial failed.",
           "`event_budget`, `timeout`, `wave_budget`, and `no_factor` remain in denominators.", "",
           "| Family | bits | Algorithm | Success/trials | Status counts | Median success events |",
           "|---|---:|---|---:|---|---:|"]
    for (family, bits, algorithm), group in sorted(grouped.items()):
        counts = Counter(r["status"] for r in group)
        success = [r["total_events"] for r in group if r["status"] == "success"]
        median = str(statistics.median(success)) if success else "—"
        outcomes = ", ".join(f"{k}:{v}" for k, v in sorted(counts.items()))
        out.append(f"| {family} | {bits} | {algorithm} | {len(success)}/{len(group)} | {outcomes} | {median} |")
    composites = [r for r in rows if r["composite"]]
    out += ["", f"Composite trials: {len(composites)}; successes: "
            f"{sum(r['status'] == 'success' for r in composites)}.",
            "Prime/0/1 controls are outside the composite-input contract; failure on these is not a factoring counterexample.",
            "", "Next: review the hypothesis's preregistered falsifier and inspect results.jsonl.",
            "Record rejected, revised, promising, or inconclusive in a finding; update research/STATE.md.",
            "A passed screen still needs unseen instances, matched baselines, and proofs.", ""]
    return "\n".join(out)


def source_files() -> list[Path]:
    files = []
    for folder in ("factoring_lab", "Factoring", "scripts", "tests", "docs"):
        files.extend(p for p in (ROOT / folder).rglob("*")
                     if p.is_file() and "__pycache__" not in p.parts)
    files.extend(ROOT / name for name in
                 ("Factoring.lean", "Audit.lean", "lean-toolchain", "lakefile.toml", "RESEARCH_LOOP.md"))
    return sorted(files)


def iterate(config_path: Path, hypothesis: str, output: Path | None = None) -> Path:
    if not re.fullmatch(r"H[0-9]{3}", hypothesis):
        raise ValueError("hypothesis must have the form H001")
    card = ROOT / "research" / "hypotheses" / f"{hypothesis}.md"
    if not card.is_file():
        raise ValueError(f"preregister a hypothesis first: {card}")
    c = json.loads(config_path.read_text())
    validate_config(c)
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = output or ROOT / "research" / "runs" / f"{stamp}-{hypothesis}"
    out.mkdir(parents=True, exist_ok=False)
    (out / "config.json").write_text(json.dumps(c, indent=2) + "\n")
    (out / "hypothesis.md").write_bytes(card.read_bytes())
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in source_files()}
    # Freeze exact sources, not only a mutable checkout's git revision.
    for relative in hashes:
        target = out / "source" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((ROOT / relative).read_bytes())
    start = time.perf_counter()
    cases = generate(c)
    setup_seconds = time.perf_counter() - start
    (out / "corpus.json").write_text(json.dumps(cases, indent=2) + "\n")
    rows = []
    deadline = start + c["total_seconds"]
    with (out / "results.jsonl").open("w") as stream:
        for case in cases:
            for seed in c["algorithm_seeds"]:
                for algorithm in c["algorithms"]:
                    left = deadline - time.perf_counter()
                    result = ({"status": "wave_budget", "detail": "whole wave deadline reached"}
                              if left <= 0 else run_one(algorithm, case["n"], seed, c,
                                                       min(left, c["timeout_seconds"])))
                    row = {k: case[k] for k in ("id", "n", "bits", "family", "composite")}
                    row.update(algorithm=algorithm, seed=seed, **result)
                    stream.write(json.dumps(row, sort_keys=True) + "\n")
                    stream.flush()
                    rows.append(row)
    (out / "report.md").write_text(summary_text(rows))
    manifest = {"schema": 1, "created_utc": stamp, "hypothesis": hypothesis,
                "python": sys.version, "platform": platform.platform(),
                "executable": sys.executable, "corpus_setup_seconds": setup_seconds,
                "wave_seconds": time.perf_counter() - start, "source_sha256": hashes,
                "artifacts_sha256": {name: digest(out / name) for name in
                                     ("config.json", "hypothesis.md", "corpus.json", "results.jsonl", "report.md")},
                "sources_unchanged_during_run": all(digest(ROOT / p) == h for p, h in hashes.items()),
                "limitations": ["event counts are not bit-operation bounds", "development corpus is public",
                                "trusted candidates only; no OS security sandbox", "timings include tracemalloc overhead"]}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return out


def verify_run(folder: Path) -> None:
    manifest = json.loads((folder / "manifest.json").read_text())
    for name, expected in manifest["artifacts_sha256"].items():
        if digest(folder / name) != expected:
            raise ValueError(f"artifact hash mismatch: {name}")
    for name, expected in manifest["source_sha256"].items():
        if digest(folder / "source" / name) != expected:
            raise ValueError(f"source hash mismatch: {name}")
    if not manifest["sources_unchanged_during_run"]:
        raise ValueError("sources changed while the experiment was running")
    rows = [json.loads(line) for line in (folder / "results.jsonl").read_text().splitlines()]
    for row in rows:
        if row["status"] == "success" and not valid_factor(row["n"], row.get("factor")):
            raise ValueError(f"invalid recorded factor: {row['id']}")

