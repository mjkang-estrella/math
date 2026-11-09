#!/usr/bin/env python3
"""Read-only exact-selection verifier; explicit detached anchors are mandatory.
Integrity only. No mathematical, source-truth, contribution or acceptance gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath

EXCLUDED = {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}

def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def inventory(root):
    found = {}
    for current, dirs, files in os.walk(root, followlinks=False):
        for name in dirs + files:
            p = Path(current) / name
            if p.is_symlink():
                raise ValueError("symlink forbidden: " + str(p.relative_to(root)))
        for name in files:
            p = Path(current) / name
            rel = p.relative_to(root).as_posix()
            if rel not in EXCLUDED:
                found[rel] = p
    return found

def verify(root, final_sha256, manifest_sha256, report_sha256):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError("root must be a real directory")
    for name, expected in [("FINAL.md", final_sha256),
                           ("MANIFEST.json", manifest_sha256),
                           ("REPORT.md", report_sha256)]:
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("invalid explicit SHA256 anchor: " + name)
        path = root / name
        if path.is_symlink() or digest(path) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    if manifest.get("schema") != "r162ac-exact-selection-v1":
        raise ValueError("unknown schema")
    if set(manifest.get("excluded_root_files", [])) != EXCLUDED:
        raise ValueError("unexpected excluded paths")
    entries = manifest["files"]
    expected = {}
    for row in entries:
        name = row["path"]
        parts = PurePosixPath(name)
        if parts.is_absolute() or ".." in parts.parts or parts.as_posix() != name:
            raise ValueError("unsafe/noncanonical manifest path")
        if name in expected or name in EXCLUDED:
            raise ValueError("duplicate or excluded manifest path")
        expected[name] = row
    actual = inventory(root)
    if set(actual) != set(expected):
        raise ValueError("exact membership mismatch; missing=" + str(sorted(set(expected)-set(actual)))
                         + "; extra=" + str(sorted(set(actual)-set(expected))))
    if expected.get("FINAL.md", {}).get("sha256") != final_sha256:
        raise ValueError("FINAL anchor not bound in manifest")
    for name, path in actual.items():
        row = expected[name]
        if path.stat().st_size != row["bytes"] or digest(path) != row["sha256"]:
            raise ValueError("member mismatch: " + name)
    return {"artifact_integrity": "verified", "files": len(actual),
            "bytes": sum(p.stat().st_size for p in actual.values()),
            "mathematical_gate": False}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    args = ap.parse_args()
    try:
        print(json.dumps(verify(args.root, args.final_sha256,
                                args.manifest_sha256, args.report_sha256), sort_keys=True))
    except (ValueError, KeyError, OSError, TypeError) as exc:
        raise SystemExit("INTEGRITY FAILURE: " + str(exc))

if __name__ == "__main__":
    main()
