#!/usr/bin/env python3
"""Read-only verification of this locally selected packet; no mathematical gate."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(root, name):
    rel = PurePosixPath(name)
    if rel.is_absolute() or not rel.parts or any(p in (".", "..") for p in rel.parts):
        raise ValueError("unsafe selected path")
    path = root.joinpath(*rel.parts)
    if path.is_symlink() or not path.is_file():
        raise ValueError("missing or symbolic selected file: " + name)
    if root not in path.resolve().parents:
        raise ValueError("selected path escapes packet")
    return path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    a = ap.parse_args()
    root = Path(a.root).resolve()
    for name, expected in [("FINAL.md", a.final_sha256), ("MANIFEST.json", a.manifest_sha256), ("REPORT.md", a.report_sha256)]:
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise ValueError("invalid explicit detached anchor")
        if digest(safe_path(root, name).read_bytes()) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_bytes())
    records = manifest["files"]
    names = [entry["path"] for entry in records]
    if len(names) != len(set(names)):
        raise ValueError("duplicate selected path")
    total = 0
    for entry in records:
        data = safe_path(root, entry["path"]).read_bytes()
        if len(data) != entry["bytes"] or digest(data) != entry["sha256"]:
            raise ValueError("selected bytes mismatch: " + entry["path"])
        total += len(data)
    excluded = set(manifest["excluded_exact"])
    prefixes = manifest["excluded_prefixes"]
    actual = set()
    for path in root.rglob("*"):
        if path.is_file() or path.is_symlink():
            rel = path.relative_to(root).as_posix()
            if rel not in excluded and not any(rel.startswith(p) for p in prefixes):
                actual.add(rel)
    if actual != set(names):
        raise ValueError("selected file set differs from manifest")
    canonical = 0
    binding_name = manifest.get("canonical_bindings")
    if binding_name is not None:
        if binding_name not in names:
            raise ValueError("bindings are not sealed")
        for entry in json.loads(safe_path(root, binding_name).read_bytes()):
            if entry["local"] not in names:
                raise ValueError("canonical object is not selected")
            data = safe_path(root, entry["local"]).read_bytes()
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if len(data) != entry["size"] or digest(data) != entry["sha256"] or blob != entry["sha"]:
                raise ValueError("canonical blob mismatch")
            canonical += 1
    print(json.dumps({"artifact_check": "pass", "selected_files": len(names), "selected_bytes": total, "canonical_blobs": canonical, "mathematical_gate": False}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(json.dumps({"artifact_check": "fail", "reason": str(error), "mathematical_gate": False}, sort_keys=True))
        sys.exit(1)
