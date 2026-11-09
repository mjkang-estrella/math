#!/usr/bin/env python3
"""Read-only own-packet verifier. Requires externally supplied detached anchors."""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def member(root, name):
    if not isinstance(name, str):
        raise ValueError("non-string member")
    p = PurePosixPath(name)
    if not name or p.is_absolute() or str(p) != name or any(x in ("", ".", "..") for x in p.parts):
        raise ValueError("unsafe member path")
    out = root
    for part in p.parts:
        out = out / part
        if out.is_symlink():
            raise ValueError("symlink member")
    return out


def anchor(root, name, expected):
    if not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise ValueError("invalid detached anchor")
    data = member(root, name).read_bytes()
    if digest(data) != expected:
        raise ValueError("detached anchor mismatch: " + name)
    return data


def selection(root):
    result = {"FINAL.md", "verify.py"}
    packet = member(root, "packet")
    if not packet.is_dir():
        raise ValueError("missing packet directory")
    for base, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            if (Path(base) / name).is_symlink():
                raise ValueError("symlink in packet")
        for name in files:
            p = Path(base) / name
            if not p.is_file():
                raise ValueError("nonregular member")
            result.add(p.relative_to(root).as_posix())
    return result


def verify(root, final_sha, manifest_sha, report_sha):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError("invalid packet root")
    anchor(root, "FINAL.md", final_sha)
    manifest_bytes = anchor(root, "MANIFEST.json", manifest_sha)
    anchor(root, "REPORT.md", report_sha)
    doc = json.loads(manifest_bytes)
    if doc.get("schema") != "r162af-own-selection-v1":
        raise ValueError("wrong schema")
    entries = doc.get("files")
    if not isinstance(entries, list):
        raise ValueError("missing entries")
    names = []
    for row in entries:
        if not isinstance(row, dict):
            raise ValueError("invalid entry")
        name = row.get("path")
        p = member(root, name)
        if name not in ("FINAL.md", "verify.py") and not name.startswith("packet/"):
            raise ValueError("out-of-selection entry")
        data = p.read_bytes()
        if type(row.get("bytes")) is not int or row["bytes"] != len(data) or row.get("sha256") != digest(data):
            raise ValueError("member mismatch: " + name)
        names.append(name)
    if len(names) != len(set(names)) or set(names) != selection(root):
        raise ValueError("selection membership mismatch")
    allowed = {"packet", "FINAL.md", "verify.py", "MANIFEST.json", "REPORT.md", "ANCHORS.json"}
    for p in root.iterdir():
        if p.name not in allowed or p.is_symlink():
            raise ValueError("unexpected root member")
    return {"artifact_check": "PASS", "files": len(names), "bytes": sum(x["bytes"] for x in entries), "mathematical_gate": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True)
    parser.add_argument("--final-sha256", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--report-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.root, args.final_sha256, args.manifest_sha256, args.report_sha256), sort_keys=True))


if __name__ == "__main__":
    main()
