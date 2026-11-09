#!/usr/bin/env python3
"""Read-only verification of an explicit-anchor local packet; no mathematical gate."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, final_sha, manifest_sha, report_sha):
    root = root.resolve(strict=True)
    for name, anchor in [("FINAL.md", final_sha), ("MANIFEST.json", manifest_sha), ("REPORT.md", report_sha)]:
        if len(anchor) != 64 or any(c not in "0123456789abcdef" for c in anchor):
            raise ValueError("invalid explicit anchor: " + name)
        path = root / name
        if path.is_symlink() or digest(path.read_bytes()) != anchor:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest.get("format") != "r162aa-exact-selection-v1":
        raise ValueError("unknown manifest format")
    entries = manifest["entries"]
    names = [entry["path"] for entry in entries]
    if names != sorted(set(names)):
        raise ValueError("duplicate or unsorted paths")
    expected = {"FINAL.md"}
    if (root / "verify_packet.py").exists():
        expected.add("verify_packet.py")
    for path in (root / "packet").rglob("*"):
        if path.is_symlink():
            raise ValueError("symlink in packet")
        if path.is_file():
            expected.add(path.relative_to(root).as_posix())
    if set(names) != expected:
        raise ValueError("exact selection differs from packet + FINAL + verifier")
    for entry in entries:
        name = entry["path"]
        rel = PurePosixPath(name)
        if rel.is_absolute() or ".." in rel.parts or str(rel) != name:
            raise ValueError("unsafe manifest path")
        path = root / name
        for parent in [path, *path.parents]:
            if parent == root:
                break
            if parent.is_symlink():
                raise ValueError("symlink in manifest path")
        if not path.resolve(strict=True).is_relative_to(root):
            raise ValueError("path escapes root")
        data = path.read_bytes()
        if len(data) != entry["bytes"] or digest(data) != entry["sha256"]:
            raise ValueError("entry mismatch: " + name)
    return len(entries)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    try:
        count = verify(Path(args.root), args.final_sha256, args.manifest_sha256, args.report_sha256)
    except (ValueError, KeyError, OSError, TypeError) as error:
        parser.exit(1, "INTEGRITY FAILURE: " + str(error) + "\n")
    print("INTEGRITY OK: " + str(count) + " exact entries and three detached anchors; no mathematical gate.")


if __name__ == "__main__":
    main()
