#!/usr/bin/env python3
"""Read-only artifact verifier. All three detached SHA256 anchors are mandatory."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def checked_file(path, expected):
    if path.is_symlink() or not path.is_file():
        raise ValueError("not a regular nonsymlink file: " + str(path))
    data = path.read_bytes()
    if digest(data) != expected:
        raise ValueError("detached/content digest mismatch: " + str(path))
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ("packet", "manifest", "report", "final-sha256", "manifest-sha256", "report-sha256"):
        ap.add_argument("--" + key, required=True)
    args = ap.parse_args()
    for anchor in (args.final_sha256, args.manifest_sha256, args.report_sha256):
        if len(anchor) != 64 or any(ch not in "0123456789abcdef" for ch in anchor):
            raise ValueError("anchors must be explicit lowercase SHA256 hex")
    packet = Path(args.packet)
    if packet.is_symlink() or not packet.is_dir():
        raise ValueError("packet must be a nonsymlink directory")
    raw = checked_file(Path(args.manifest), args.manifest_sha256)
    checked_file(Path(args.report), args.report_sha256)
    checked_file(packet / "FINAL.md", args.final_sha256)
    manifest = json.loads(raw)
    if manifest.get("algorithm") != "sha256":
        raise ValueError("unexpected manifest algorithm")
    expected = set()
    for item in manifest["files"]:
        name = item["path"]
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or rel.as_posix() != name or not rel.parts:
            raise ValueError("unsafe/noncanonical manifest path")
        if name in expected:
            raise ValueError("duplicate manifest path")
        expected.add(name)
        path = packet
        for part in rel.parts:
            path = path / part
            if path.is_symlink():
                raise ValueError("symlink in packet")
        data = checked_file(path, item["sha256"])
        if len(data) != item["bytes"]:
            raise ValueError("size mismatch: " + name)
    actual = set()
    for path in packet.rglob("*"):
        if path.is_symlink():
            raise ValueError("symlink in packet")
        if path.is_file():
            actual.add(path.relative_to(packet).as_posix())
    if actual != expected:
        raise ValueError("packet inventory differs from exact manifest")
    if "FINAL.md" not in expected:
        raise ValueError("FINAL.md absent from manifest")
    print(json.dumps({"artifact_integrity": "matched", "files": len(expected), "mathematical_gate": False}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
