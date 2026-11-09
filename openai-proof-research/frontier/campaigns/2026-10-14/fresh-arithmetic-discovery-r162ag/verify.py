#!/usr/bin/env python3
"""Read-only r162ag artifact verification with three explicit detached anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(root, name):
    if not isinstance(name, str):
        raise ValueError("non-string path")
    p = PurePosixPath(name)
    if not name or p.is_absolute() or str(p) != name or ".." in p.parts:
        raise ValueError("unsafe path")
    current = root
    for part in p.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("symlink")
    return current


def check(root, final_hash, manifest_hash, report_hash):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError("invalid root")
    data = {}
    for name, expected in [("FINAL.md", final_hash), ("MANIFEST.json", manifest_hash), ("REPORT.md", report_hash)]:
        data[name] = safe(root, name).read_bytes()
        if len(expected) != 64 or sha(data[name]) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads(data["MANIFEST.json"])
    if manifest.get("schema") != "r162ag-own-v1":
        raise ValueError("wrong schema")
    entries = manifest["files"]
    names = []
    for row in entries:
        name = row["path"]
        p = safe(root, name)
        if name not in ("FINAL.md", "verify.py") and not name.startswith("packet/"):
            raise ValueError("outside selection")
        b = p.read_bytes()
        if type(row["bytes"]) is not int or len(b) != row["bytes"] or sha(b) != row["sha256"]:
            raise ValueError("member changed: " + name)
        names.append(name)
    actual = {"FINAL.md", "verify.py"}
    packet = safe(root, "packet")
    if not packet.is_dir():
        raise ValueError("missing packet")
    for base, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            if (Path(base) / name).is_symlink():
                raise ValueError("packet symlink")
        for name in files:
            p = Path(base) / name
            if not p.is_file():
                raise ValueError("nonregular file")
            actual.add(p.relative_to(root).as_posix())
    if len(names) != len(set(names)) or set(names) != actual:
        raise ValueError("membership mismatch")
    allowed = {"packet", "FINAL.md", "verify.py", "MANIFEST.json", "REPORT.md", "ANCHORS.json"}
    for p in root.iterdir():
        if p.name not in allowed or p.is_symlink():
            raise ValueError("unexpected root entry")
    return {"artifact_check": "PASS", "files": len(names), "bytes": sum(row["bytes"] for row in entries), "mathematical_gate": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256), sort_keys=True))
