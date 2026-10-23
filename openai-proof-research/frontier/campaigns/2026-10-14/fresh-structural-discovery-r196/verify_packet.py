#!/usr/bin/env python3
"""Read-only verification against three explicitly supplied detached anchors."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re


def sha(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root).resolve(strict=True)
    for filename, expected in [("FINAL.md", final_sha256), ("MANIFEST.json", manifest_sha256), ("REPORT.md", report_sha256)]:
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("invalid explicit anchor: " + filename)
        p = root / filename
        if p.is_symlink() or sha(p.read_bytes()) != expected:
            raise ValueError("detached anchor mismatch: " + filename)
    manifest = json.loads((root / "MANIFEST.json").read_bytes())
    if manifest.get("format") != "r196-selected-packet-v1":
        raise ValueError("unexpected manifest format")
    seen = set()
    for item in manifest["files"]:
        name = item["path"]
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or str(rel) != name or not rel.parts:
            raise ValueError("unsafe selected path")
        if name in seen or name in {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}:
            raise ValueError("duplicate or detached file selected: " + name)
        seen.add(name)
        p = root.joinpath(*rel.parts)
        current = root
        for part in rel.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError("symlink in selected path: " + name)
        if not p.resolve(strict=True).is_relative_to(root):
            raise ValueError("path escaped selected root")
        data = p.read_bytes()
        if len(data) != item["bytes"] or sha(data) != item["sha256"]:
            raise ValueError("selected byte mismatch: " + name)
    if "FINAL.md" not in seen or "FROZEN.md" not in seen:
        raise ValueError("missing required selected anchors")
    return {"artifact_integrity": "matched supplied anchors", "selected_files": len(seen), "mathematical_grade": None}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    try:
        print(json.dumps(verify(**vars(args)), sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print("integrity error: " + str(exc), file=sys.stderr)
        sys.exit(1)
