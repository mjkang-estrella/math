#!/usr/bin/env python3
"""Read-only packet verifier. Trust must enter as three explicit detached hashes."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def regular(root, relative):
    posix = PurePosixPath(relative)
    if not relative or posix.is_absolute() or str(posix) != relative or any(x in (".", "..") for x in posix.parts):
        raise ValueError("unsafe/noncanonical path: " + relative)
    p = root
    for component in posix.parts:
        p = p / component
        if p.is_symlink():
            raise ValueError("symlink: " + relative)
    if not p.is_file():
        raise ValueError("not a regular file: " + relative)
    return p


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True)
    for name in ("final", "manifest", "report"):
        ap.add_argument("--" + name + "-sha256", required=True)
    args = ap.parse_args()
    root = Path(args.root).resolve(strict=True)
    for name in ("final", "manifest", "report"):
        expected = getattr(args, name + "_sha256")
        if not re.fullmatch("[0-9a-f]{64}", expected):
            raise ValueError("invalid explicit " + name + " anchor")
        filename = name.upper() + (".json" if name == "manifest" else ".md")
        if sha(regular(root, filename).read_bytes()) != expected:
            raise ValueError("detached anchor mismatch: " + filename)
    manifest = json.loads(regular(root, "MANIFEST.json").read_text(encoding="utf-8"))
    if manifest.get("schema") != "r170-selected-packet-v1":
        raise ValueError("unknown manifest schema")
    seen = set()
    for entry in manifest["files"]:
        relative = entry["path"]
        if relative in seen or relative in ("MANIFEST.json", "REPORT.md", "ANCHORS.json"):
            raise ValueError("duplicate or detached entry: " + relative)
        seen.add(relative)
        data = regular(root, relative).read_bytes()
        if len(data) != entry["bytes"] or sha(data) != entry["sha256"]:
            raise ValueError("selected file mismatch: " + relative)
    if "FINAL.md" not in seen:
        raise ValueError("FINAL.md is not in selected packet")
    print(json.dumps({"artifact_integrity": "verified", "selected_files": len(seen),
                      "mathematical_verdict": "none", "writes": 0}))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print("VERIFICATION FAILED: " + str(exc), file=sys.stderr)
        sys.exit(1)
