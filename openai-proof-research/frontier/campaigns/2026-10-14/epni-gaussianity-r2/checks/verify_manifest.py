#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT.

Read-only integrity verifier for epni-gaussianity-r2.
It recomputes hashes and reruns the rational checks.
It does not fetch, reseal, or write any shared index.
"""

from __future__ import annotations

import hashlib
import json
import runpy
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ROUND1_CANDIDATE = (
    "8c227f21c39e205f8cf95d58f03d82bb06ed7a4e63cdbbe04336d82a8b88353d"
)
COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode()
    return hashlib.sha1(header + data).hexdigest()


def check_record(record: dict) -> None:
    path = ROOT / record["path"]
    if not path.resolve().is_relative_to(ROOT.resolve()):
        raise SystemExit(f"path escapes root: {record['path']}")
    data = path.read_bytes()
    if len(data) != record["bytes"]:
        raise SystemExit(f"size mismatch: {record['path']}")
    if digest(data) != record["sha256"]:
        raise SystemExit(f"sha256 mismatch: {record['path']}")


def passage(raw: bytes, start: int, end: int) -> bytes:
    lines = raw.decode().splitlines()
    if not 1 <= start <= end <= len(lines):
        raise SystemExit(f"bad extent {start}-{end} of {len(lines)} lines")
    return ("\n".join(lines[start - 1 : end]) + "\n").encode()


def main() -> None:
    sys.dont_write_bytecode = True
    runpy.run_path(str(ROOT / "checks" / "check.py"), run_name="__main__")

    seal = json.loads((ROOT / "seal.json").read_text())
    actual = {
        str(p.relative_to(ROOT))
        for p in ROOT.rglob("*")
        if p.is_file()
    }
    expected = {record["path"] for record in seal["files"]}
    if actual != expected | {"seal.json"}:
        missing = sorted(actual - expected - {"seal.json"})
        extra = sorted(expected - actual)
        raise SystemExit(f"inventory mismatch missing={missing} extra={extra}")
    if len(expected) != len(seal["files"]):
        raise SystemExit("duplicate seal paths")
    for record in seal["files"]:
        check_record(record)

    inputs = json.loads((ROOT / "inputs-manifest.json").read_text())
    outputs = json.loads((ROOT / "outputs-manifest.json").read_text())
    left = {record["path"] for record in inputs["files"]}
    right = {record["path"] for record in outputs["files"]}
    if left & right:
        raise SystemExit("input/output overlap")
    if left | right != expected - {"outputs-manifest.json"}:
        raise SystemExit("manifest partition mismatch")
    if left != {path for path in expected if path.startswith("inputs/")}:
        raise SystemExit("inputs manifest is not exactly inputs/")
    for record in inputs["files"] + outputs["files"]:
        check_record(record)

    fetched = json.loads((ROOT / "receipts" / "fetch.json").read_text())
    for record in fetched["upstream"]:
        data = (ROOT / record["local"]).read_bytes()
        if len(data) != record["bytes"] or digest(data) != record["sha256"]:
            raise SystemExit(f"upstream hash mismatch: {record['local']}")
        if git_blob(data) != record["git_blob_sha1"]:
            raise SystemExit(f"git blob mismatch: {record['local']}")
        url = (
            "https://raw.githubusercontent.com/openai/math/"
            + COMMIT
            + "/"
            + record["path"]
        )
        if record["url"] != url:
            raise SystemExit(f"url mismatch: {record['local']}")
    round1 = (ROOT / "inputs/round1/candidate.md").read_bytes()
    if digest(round1) != ROUND1_CANDIDATE:
        raise SystemExit("round-1 candidate digest changed")
    if digest(round1) != fetched["round1_candidate_sha256"]:
        raise SystemExit("fetch receipt round-1 digest mismatch")
    for record in fetched["literature_copies"]:
        data = (ROOT / record["local"]).read_bytes()
        if len(data) != record["bytes"] or digest(data) != record["sha256"]:
            raise SystemExit(f"literature hash mismatch: {record['local']}")

    reading = json.loads((ROOT / "receipts" / "read-extents.json").read_text())
    for record in reading["readings"]:
        raw = (ROOT / record["path"]).read_bytes()
        if digest(raw) != record["sha256"]:
            raise SystemExit(f"reading hash mismatch: {record['path']}")
        for extent in record["extents"]:
            got = digest(passage(raw, extent["start_line"], extent["end_line"]))
            if got != extent["passage_sha256"]:
                raise SystemExit(
                    f"passage mismatch: {record['path']} "
                    f"{extent['start_line']}-{extent['end_line']}"
                )

    checks = json.loads((ROOT / "receipts" / "checks.json").read_text())
    if checks.get("status") != "pass":
        raise SystemExit("checks receipt is not pass")
    print(
        f"PASS: {len(inputs['files'])} inputs, "
        f"{len(outputs['files'])} output records, "
        f"{len(fetched['upstream'])} pinned sections, "
        f"{len(reading['readings'])} reading records"
    )


if __name__ == "__main__":
    main()
