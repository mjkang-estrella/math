#!/usr/bin/env python3
"""Bounded artifact mutations on a disposable copy; no mathematical inference."""
import argparse
import datetime
import fnmatch
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def forbidden(name):
    s = name.lower()
    return any(fnmatch.fnmatch(s, p) for p in (
        "t205q140-*", "k369r134-contribution-*", "k369r134-proof-*",
        "*arithmetic*r104*", "*structural*r141*",
    )) or ("r141" in s and "brief" in s)


def vector(root):
    result = {}
    for base, dirs, files in os.walk(root / "packet", followlinks=False):
        if any(forbidden(n) for n in dirs + files):
            raise ValueError("excluded component in artifact tree")
        for name in files:
            p = Path(base) / name
            if p.is_symlink():
                raise ValueError("symlink in baseline")
            result[p.relative_to(root).as_posix()] = sha(p)
    for name in ("FINAL.json", "MANIFEST.json", "REPORT.md", "verify.py"):
        result[name] = sha(root / name)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True, type=Path)
    for n in ("final", "manifest", "report"):
        ap.add_argument("--" + n + "-sha256", required=True)
    ap.add_argument("--receipt", required=True, type=Path)
    args = ap.parse_args()
    root = args.root.resolve()
    receipt = args.receipt.resolve()
    receipt.relative_to(root)
    before = vector(root)
    verifier_args = [
        "--final-sha256", args.final_sha256,
        "--manifest-sha256", args.manifest_sha256,
        "--report-sha256", args.report_sha256,
    ]
    cases = []

    def check(name, target, expected):
        p = subprocess.run(
            [sys.executable, "-B", str(target / "verify.py"), "--root", str(target),
             *verifier_args], capture_output=True, text=True, timeout=30,
        )
        passed = (p.returncode == 0) == expected
        cases.append(dict(name=name, expected_pass=expected, expected_outcome=passed,
                          returncode=p.returncode, stdout=p.stdout.strip(),
                          stderr=p.stderr.strip()))
        if not passed:
            raise AssertionError(name)

    work = root / "work"
    work.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="review-controls-", dir=work) as tmp:
        copy = Path(tmp)
        shutil.copytree(root / "packet", copy / "packet")
        for n in ("FINAL.json", "MANIFEST.json", "REPORT.md", "verify.py"):
            shutil.copy2(root / n, copy / n)
        check("copied_baseline", copy, True)
        p = copy / "packet/public/review.md"
        b = p.read_bytes()
        p.write_bytes(b + b"\nmutation\n")
        check("review_payload_mutation", copy, False)
        p.write_bytes(b)
        p = copy / "packet/unmanifested.txt"
        p.write_text("mutation\n")
        check("extra_payload", copy, False)
        p.unlink()
        p = copy / "verify.py"
        b = p.read_bytes()
        p.write_bytes(b + b"\n# mutation\n")
        check("verifier_mutation", copy, False)
        p.write_bytes(b)
        p = copy / "packet/public/review.md"
        p.write_bytes(p.read_bytes() + b"\nforged reseal\n")
        manifest = json.loads((copy / "MANIFEST.json").read_text())
        for row in manifest["files"]:
            f = copy / row["path"]
            row.update(bytes=f.stat().st_size, sha256=sha(f))
        (copy / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
        final = json.loads((copy / "FINAL.json").read_text())
        final["manifest_sha256"] = sha(copy / "MANIFEST.json")
        (copy / "FINAL.json").write_text(json.dumps(final, indent=2) + "\n")
        check("forged_reseal_detached_anchors", copy, False)
    check("original_after_disposable_mutations", root, True)
    after = vector(root)
    assert before == after
    receipt.write_text(json.dumps({
        "observed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "status": "PASS_ARTIFACT_CONTROLS_ONLY",
        "cases": cases, "packet_and_bound_outer_files_unchanged": True,
        "copy_removed": True,
        "limits": "File-identity controls only. No mathematical, contribution, acceptance, "
                  "formal, manuscript, or release gate. No syscall denial or per-case "
                  "original-preservation assertion.",
    }, indent=2) + "\n")
    print(json.dumps({"artifact_cases": len(cases), "negative_cases": 4,
                      "all_expected": True, "mathematical_gate": False}))


if __name__ == "__main__":
    main()
