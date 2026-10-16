#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Fail-closed release runner for the cr(K_n - e) manuscript package.

Runs, from the package root:
  1. support/release_checks.py (new exact checks, enforced controls);
  2. an unchanged copy of the candidate author's stdlib checker;
  3. an unchanged copy of the independent proof reviewer's checker;
  4. optionally (--large-python, --large-n), an unchanged copy of the author's
     mod-p NumPy checker for chosen n.

Any nonzero exit status, any output line reporting FAIL, a missing success
line, or a mismatch with the frozen expected output makes this runner exit 1.
The author's mod-p checker prints "SOME FAIL" and still exits 0 when a check
fails; this runner treats that output as a failure.

Inherited scripts run in fresh directories checks/work-*/ so that their
side outputs never touch the frozen originals.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
INHERITED = ROOT / "support" / "inherited"
CHECKS = ROOT / "checks"

EXPECTED_SHA256 = {
    # fresh-substantial-discovery-r2/output-manifest.json
    "author/kn_minus_e_checks.py": "1ee907a1779184faa3fe1b3c229d83d7332bedeb956f900ca8164901633f3364",
    "author/kn_minus_e_checks.out": "bc5cbf6900104a6bc05cb0c9df99ddf5750281484a488c372aea0c1ceac5d3fe",
    "author/kn_minus_e_modp_large.py": "18cfe155119d6d407cb7d26b5d9ec92660388165622df4bf1fae0d780ef94386",
    "author/kn_minus_e_modp_large.out": "35f2508e427869ad5a4f9825e63869d03c6ef0377e437eba21e31f23165df20f",
    # kn-minus-edge-parent/proof-r1-verification.json and kn-minus-edge-proof-r1 manifests
    "reviewer/adversarial.py": "49d327f68c2841933bf2bc9f208e080af474b6c83c0e8ceca9a64985543ebcf1",
    "reviewer/adversarial.out": "b27e836235ce25233fad65e00cd08a703a7dd6c2bbadd1c4a235c643647994ab",
    "reviewer/adversarial.json": "45f868c8e6381e9c2cfa3b597be6f9b0fd6ffbd71755c8ac00eb758fb4a30691",
}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def classify(returncode, stdout, success_line):
    """Return a list of reasons for failure (empty means pass)."""
    reasons = []
    if returncode != 0:
        reasons.append(f"exit status {returncode}")
    lines = stdout.splitlines()
    bad = [line for line in lines if "FAIL" in line]
    if bad:
        reasons.append(f"failure lines: {bad[:5]}")
    if success_line not in lines:
        reasons.append(f"missing success line {success_line!r}")
    return reasons


def self_test_classifier():
    cases = [
        ((0, "n=15 rect: ... -> FAIL\nSOME FAIL\n", "ALL OK"), False),
        ((0, "n=15 rect: ... -> ok\nALL OK\n", "ALL OK"), True),
        ((1, "ALL OK\n", "ALL OK"), False),
        ((0, "n=15 rect: ... -> ok\n", "ALL OK"), False),
    ]
    return all((not classify(*args)) == expected for args, expected in cases)


def clean_env():
    env = {k: v for k, v in os.environ.items() if not k.startswith("PYTHON")}
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def run(cmd, cwd, timeout):
    start = time.monotonic()
    proc = subprocess.run(cmd, cwd=cwd, env=clean_env(), stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout)
    return proc, round(time.monotonic() - start, 1)


def fresh_workdir(name):
    work = CHECKS / f"work-{name}"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    return work


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--python", default=sys.executable, help="interpreter for stdlib checks")
    parser.add_argument("--large-python", default=None, help="interpreter with NumPy for the mod-p checker")
    parser.add_argument("--large-n", type=int, nargs="*", default=[], help="orders for the mod-p checker")
    parser.add_argument("--large-only", action="store_true",
                        help="run only the optional mod-p step (separate receipt)")
    args = parser.parse_args()

    receipt = {"runner": "support/run_all.py", "runner_sha256": sha256(__file__),
               "platform": platform.platform(), "steps": [], "status": None}
    failures = []

    if sys.flags.optimize:
        failures.append("runner started with -O; assertions in inherited checkers would be disabled")

    ok = self_test_classifier()
    receipt["steps"].append({"step": "classifier self-test (SOME FAIL with exit 0 must be rejected)",
                             "status": "PASS" if ok else "FAIL"})
    if not ok:
        failures.append("classifier self-test")

    auth = {}
    for rel, expected in EXPECTED_SHA256.items():
        actual = sha256(INHERITED / rel)
        auth[rel] = {"sha256": actual, "matches_frozen_record": actual == expected}
        if actual != expected:
            failures.append(f"inherited copy hash mismatch: {rel}")
    receipt["steps"].append({"step": "authenticate inherited copies", "files": auth})

    version = subprocess.check_output([args.python, "-c", "import sys; print(sys.version.split()[0])"],
                                      env=clean_env()).decode().strip()
    receipt["python"] = {"path": args.python, "version": version}

    # 1. New release checks.
    if not args.large_only:
        proc, seconds = run([args.python, "-B", str(ROOT / "support" / "release_checks.py"),
                             str(CHECKS / "release_checks.json")], ROOT, 3600)
        out = proc.stdout.decode()
        (CHECKS / "release_checks.out").write_text(out)
        reasons = classify(proc.returncode, out, "RELEASE CHECKS PASSED")
        if proc.stderr:
            reasons.append("stderr not empty")
        receipt["steps"].append({"step": "support/release_checks.py", "exit": proc.returncode, "seconds": seconds,
                                 "stdout": "checks/release_checks.out",
                                 "stdout_sha256": hashlib.sha256(proc.stdout).hexdigest(),
                                 "status": "PASS" if not reasons else "FAIL", "reasons": reasons})
        failures += [f"release_checks: {r}" for r in reasons]

    if not args.large_only:
        # 2. Author stdlib checker (exact rationals; float geometry; modular ranks).
        work = fresh_workdir("author")
        shutil.copyfile(INHERITED / "author" / "kn_minus_e_checks.py", work / "kn_minus_e_checks.py")
        proc, seconds = run([args.python, "-B", "kn_minus_e_checks.py"], work, 3600)
        out = proc.stdout.decode()
        (CHECKS / "author-checks.out").write_text(out)
        frozen = (INHERITED / "author" / "kn_minus_e_checks.out").read_text()
        frozen_science = frozen.split("\n\nreal\t")[0] + "\n"
        reasons = classify(proc.returncode, out, "ALL CHECKS PASSED")
        identical = out == frozen_science
        if not identical:
            reasons.append("stdout differs from frozen output (timing footer excluded)")
        if proc.stderr:
            reasons.append("stderr not empty")
        receipt["steps"].append({"step": "inherited author checker kn_minus_e_checks.py (unchanged copy)",
                                 "exit": proc.returncode, "seconds": seconds,
                                 "stdout": "checks/author-checks.out",
                                 "stdout_identical_to_frozen_without_timing_footer": identical,
                                 "status": "PASS" if not reasons else "FAIL", "reasons": reasons})
        failures += [f"author checker: {r}" for r in reasons]

        # 3. Independent reviewer checker.
        work = fresh_workdir("reviewer")
        shutil.copyfile(INHERITED / "reviewer" / "adversarial.py", work / "adversarial.py")
        proc, seconds = run([args.python, "-B", "adversarial.py"], work, 3600)
        out = proc.stdout.decode()
        (CHECKS / "reviewer-adversarial.out").write_text(out)
        reasons = classify(proc.returncode, out, "ALL INDEPENDENT CHECKS PASSED")
        identical = proc.stdout == (INHERITED / "reviewer" / "adversarial.out").read_bytes()
        if not identical:
            reasons.append("stdout differs from frozen output")
        json_same = False
        produced = work / "adversarial.json"
        if produced.exists():
            new = json.loads(produced.read_text())
            old = json.loads((INHERITED / "reviewer" / "adversarial.json").read_text())
            new.pop("runtime_seconds", None)
            old.pop("runtime_seconds", None)
            json_same = new == old
            shutil.copyfile(produced, CHECKS / "reviewer-adversarial.json")
        if not json_same:
            reasons.append("adversarial.json differs from frozen record (runtime excluded)")
        if proc.stderr:
            reasons.append("stderr not empty")
        receipt["steps"].append({"step": "inherited reviewer checker adversarial.py (unchanged copy)",
                                 "exit": proc.returncode, "seconds": seconds,
                                 "stdout": "checks/reviewer-adversarial.out",
                                 "stdout_byte_identical_to_frozen": identical,
                                 "json_identical_except_runtime": json_same,
                                 "status": "PASS" if not reasons else "FAIL", "reasons": reasons})
        failures += [f"reviewer checker: {r}" for r in reasons]

    # 4. Optional author mod-p checker (NumPy, p = 2^31 - 1).
    if args.large_only and not args.large_n:
        failures.append("--large-only requires --large-n")
    if args.large_n:
        if not args.large_python:
            failures.append("--large-n given without --large-python")
        else:
            work = fresh_workdir("author-modp")
            for name in ("kn_minus_e_checks.py", "kn_minus_e_modp_large.py"):
                shutil.copyfile(INHERITED / "author" / name, work / name)
            cmd = [args.large_python, "-B", "kn_minus_e_modp_large.py"] + [str(n) for n in args.large_n]
            proc, seconds = run(cmd, work, 6 * 3600)
            out = proc.stdout.decode()
            (CHECKS / "author-modp.out").write_text(out)
            reasons = classify(proc.returncode, out, "ALL OK")
            frozen_lines = set((INHERITED / "author" / "kn_minus_e_modp_large.out").read_text().splitlines())
            produced = [line for line in out.splitlines() if line.startswith("n=")]
            if len(produced) != 2 * len(args.large_n):
                reasons.append(f"expected {2 * len(args.large_n)} result lines, got {len(produced)}")
            unmatched = [line for line in produced if line not in frozen_lines]
            if unmatched:
                reasons.append(f"lines not in frozen output: {unmatched}")
            if proc.stderr:
                reasons.append("stderr not empty")
            numpy_version = subprocess.check_output(
                [args.large_python, "-c", "import numpy; print(numpy.__version__)"], env=clean_env()).decode().strip()
            receipt["steps"].append({"step": "inherited author mod-p checker (unchanged copy)",
                                     "orders": args.large_n, "numpy": numpy_version,
                                     "interpreter": args.large_python, "exit": proc.returncode,
                                     "seconds": seconds, "stdout": "checks/author-modp.out",
                                     "lines_match_frozen": not unmatched,
                                     "status": "PASS" if not reasons else "FAIL", "reasons": reasons})
            failures += [f"author mod-p checker: {r}" for r in reasons]

    receipt["failures"] = failures
    receipt["status"] = "PASS" if not failures else "FAIL"
    name = "run-receipt-large.json" if args.large_only else "run-receipt.json"
    (CHECKS / name).write_text(json.dumps(receipt, indent=2) + "\n")
    for work in CHECKS.glob("work-*"):
        if (work.name == "work-author-modp") == args.large_only:
            shutil.rmtree(work, ignore_errors=True)
    if failures:
        print("RUN FAILED")
        for f in failures:
            print("  " + f)
        sys.exit(1)
    print(f"RUN PASSED ({name})")


if __name__ == "__main__":
    main()
