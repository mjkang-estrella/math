#!/usr/bin/env python3
"""Read-only exact-packet check. All three trust anchors are required externally."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

CARRIERS = {"private/MANIFEST.json", "REPORT.md", "ANCHORS.json"}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, supplied):
    root = root.resolve(strict=True)
    for name, expected in supplied.items():
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("invalid external SHA256 anchor")
        if sha((root / name).read_bytes()) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "private/MANIFEST.json").read_bytes())
    if manifest.get("schema") != "r192-exact-packet-v1":
        raise ValueError("unknown manifest schema")
    entries = {}
    for entry in manifest["files"]:
        name = entry["path"]
        pp = PurePosixPath(name)
        if pp.is_absolute() or ".." in pp.parts or str(pp) != name or name in CARRIERS or name in entries:
            raise ValueError("invalid or duplicated payload path: " + name)
        entries[name] = entry
    actual = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError("symlink disallowed: " + str(path))
        if path.is_file():
            name = path.relative_to(root).as_posix()
            if name not in CARRIERS:
                actual.add(name)
    if actual != set(entries):
        raise ValueError("payload inventory mismatch; missing=" + repr(sorted(set(entries)-actual)) + "; extra=" + repr(sorted(actual-set(entries))))
    for name, entry in entries.items():
        data = (root / name).read_bytes()
        if len(data) != entry["bytes"] or sha(data) != entry["sha256"]:
            raise ValueError("payload mismatch: " + name)
    carrier = root / "ANCHORS.json"
    if carrier.exists() and json.loads(carrier.read_bytes()) != supplied:
        raise ValueError("anchor carrier differs from explicit anchors")
    return len(entries)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    anchors = {"FINAL.md": args.final_sha256, "private/MANIFEST.json": args.manifest_sha256, "REPORT.md": args.report_sha256}
    try:
        count = verify(args.root, anchors)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, "REJECT: " + str(error) + "\n")
    print("PASS: exact payload and three explicit detached anchors; " + str(count) + " files")

if __name__ == "__main__":
    main()
