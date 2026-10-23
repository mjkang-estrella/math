#!/usr/bin/env python3
"""Read-only exact-packet integrity check; no mathematical gate."""
import argparse
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_hash(path, expected):
    actual = digest(path)
    if actual != expected:
        raise ValueError("SHA256 mismatch: " + str(path))
    return actual


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    for name, expected in (("FINAL.md", final_sha),
                           ("MANIFEST.json", manifest_sha),
                           ("REPORT.md", report_sha)):
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("An explicit lowercase detached SHA256 is required")
        check_hash(root / name, expected)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest.get("format") != "r162q-exact-packet-v1":
        raise ValueError("Unknown manifest format")
    entries = manifest["files"]
    expected_paths = set()
    for entry in entries:
        rel = Path(entry["path"])
        if rel.is_absolute() or ".." in rel.parts or rel.as_posix() != entry["path"]:
            raise ValueError("Unsafe or noncanonical manifest path")
        if entry["path"] in expected_paths:
            raise ValueError("Duplicate manifest path")
        expected_paths.add(entry["path"])
        path = root / rel
        if path.is_symlink() or not path.is_file():
            raise ValueError("Missing or symlink payload: " + str(rel))
        if path.stat().st_size != entry["bytes"]:
            raise ValueError("Size mismatch: " + str(rel))
        check_hash(path, entry["sha256"])
    outside = {"MANIFEST.json", "REPORT.md", "ANCHORS.json"}
    actual_paths = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError("Symlink in packet root")
        if path.is_file():
            actual_paths.add(path.relative_to(root).as_posix())
    if actual_paths != expected_paths | outside:
        raise ValueError("Exact file-set mismatch")
    required = {"FINAL.md", "verify_packet.py"}
    if not required <= expected_paths or any(
        p not in required and not p.startswith("packet/") for p in expected_paths
    ):
        raise ValueError("Payload boundary mismatch")
    print("Integrity verified: %d exact payload files; detached FINAL/MANIFEST/REPORT match. No mathematical gate." % len(entries))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha", required=True)
    parser.add_argument("--manifest-sha", required=True)
    parser.add_argument("--report-sha", required=True)
    args = parser.parse_args()
    verify(args.root, args.final_sha, args.manifest_sha, args.report_sha)
