#!/usr/bin/env python3
"""Run integrity mutations only on disposable copies under an explicit work dir."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def digest(root):
    result = []
    for p in sorted(root.rglob("*")):
        info = p.lstat()
        record = [p.relative_to(root).as_posix(), info.st_mode, info.st_nlink]
        if p.is_file():
            record.append(hashlib.sha256(p.read_bytes()).hexdigest())
        result.append(record)
    return hashlib.sha256(json.dumps(result).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--work", required=True, type=Path)
    parser.add_argument("--expected-manifest", required=True)
    parser.add_argument("--expected-report", required=True)
    args = parser.parse_args()
    original = args.packet.resolve()
    work = args.work.resolve()
    assert work != original and original not in work.parents
    assert work.parent == original.parent, "work must be sibling of owned packet"
    work.mkdir(exist_ok=True)
    verifier = original / "public/verify.py"
    before = digest(original)
    results = []
    cases = ["unchanged", "alter_payload", "missing_file", "extra_file", "extra_directory",
             "symlink", "hardlink", "alter_manifest", "resealed_payload", "wrong_anchor",
             "wrong_report", "missing_anchor"]
    for case in cases:
        with tempfile.TemporaryDirectory(prefix="control-", dir=work) as temporary:
            copy = Path(temporary) / "packet"
            shutil.copytree(original, copy)
            report = copy / "public/report.md"
            manifest = copy / "MANIFEST.json"
            if case in ("alter_payload", "resealed_payload"):
                report.write_bytes(report.read_bytes() + b"\nmutation\n")
            if case == "missing_file":
                report.unlink()
            if case == "extra_file":
                (copy / "public/unindexed.txt").write_text("extra")
            if case == "extra_directory":
                (copy / "public/unindexed-dir").mkdir()
            if case in ("symlink", "hardlink"):
                report.unlink()
                target = copy / "public/RIGHTS.md"
                if case == "symlink":
                    report.symlink_to(target)
                else:
                    os.link(target, report)
            if case == "alter_manifest":
                manifest.write_bytes(manifest.read_bytes() + b" ")
            if case == "resealed_payload":
                data = json.loads(manifest.read_bytes())
                payload = report.read_bytes()
                data["files"]["public/report.md"] = {
                    "bytes": len(payload), "sha256": hashlib.sha256(payload).hexdigest()}
                manifest.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
            command = [sys.executable, "-B", str(verifier), "--packet", str(copy),
                       "--expected-report", "0" * 64 if case == "wrong_report" else args.expected_report]
            if case != "missing_anchor":
                command += ["--expected-manifest",
                            "0" * 64 if case == "wrong_anchor" else args.expected_manifest]
            process = subprocess.run(command, capture_output=True, text=True, timeout=30)
            accepted = process.returncode == 0
            assert accepted == (case == "unchanged"), (case, process.stdout, process.stderr)
            results.append({"case": case, "accepted": accepted,
                            "returncode": process.returncode,
                            "diagnostic": process.stderr.strip()[-400:]})
    after = digest(original)
    assert before == after, "original packet changed"
    print(json.dumps({"purpose": "integrity controls, not mathematical gates",
                      "manifest_sha256": args.expected_manifest,
                      "report_sha256": args.expected_report,
                      "original_digest_before": before, "original_digest_after": after,
                      "original_unchanged": True, "cases": results}, indent=2))


if __name__ == "__main__":
    main()
