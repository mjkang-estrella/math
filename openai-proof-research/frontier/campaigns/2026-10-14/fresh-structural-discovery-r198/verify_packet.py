#!/usr/bin/env python3
"""Read-only artifact verification. All three detached SHA256 anchors are required.
This tool checks exact bytes/selection/modes; it does not evaluate mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

sys.dont_write_bytecode = True

def demand(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def valid_anchor(value):
    demand(len(value) == 64 and all(c in "0123456789abcdef" for c in value), "invalid detached anchor")
    return value

def relative(value, directory=False):
    demand(isinstance(value, str), "non-string path")
    if directory and value == ".":
        return value
    p = PurePosixPath(value)
    demand(not p.is_absolute() and p.as_posix() == value and value not in ("", "."), "noncanonical relative path")
    demand(".." not in p.parts and "." not in p.parts and "\\" not in value, "unsafe relative path")
    return value

def regular(p):
    info = p.lstat()
    demand(stat.S_ISREG(info.st_mode), "not a regular file: " + str(p))
    return info

def run(args):
    root = Path(args.packet).absolute()
    demand(root.is_dir() and not root.is_symlink(), "packet must be an ordinary directory")
    report = Path(args.report).absolute()
    demand(not report.is_relative_to(root), "REPORT must be outside the selected packet")
    mi = regular(root / "MANIFEST.json")
    demand(stat.S_IMODE(mi.st_mode) == 0o644, "manifest mode mismatch")
    mb = (root / "MANIFEST.json").read_bytes()
    demand(digest(mb) == args.manifest_sha256, "detached MANIFEST anchor mismatch")
    manifest = json.loads(mb)
    demand(manifest.get("schema") == "r198-selected-packet-v1", "wrong manifest schema")
    files = manifest["files"]
    directories = manifest["directories"]
    expected_files = {}
    for item in files:
        name = relative(item["path"])
        demand(name != "MANIFEST.json" and name not in expected_files, "duplicate or self-included manifest entry")
        valid_anchor(item["sha256"])
        expected_files[name] = item
    demand("FINAL.md" in expected_files, "FINAL not selected")
    expected_dirs = {}
    for item in directories:
        name = relative(item["path"], True)
        demand(name not in expected_dirs, "duplicate directory entry")
        expected_dirs[name] = item["mode"]
    actual_files = set()
    actual_dirs = set()
    for here, ds, fs in os.walk(root, topdown=True, followlinks=False):
        here = Path(here)
        name = here.relative_to(root).as_posix()
        demand(not here.is_symlink(), "symlink directory")
        actual_dirs.add(name)
        demand(name in expected_dirs, "unselected directory: " + name)
        demand(stat.S_IMODE(here.stat().st_mode) == expected_dirs[name], "directory mode mismatch: " + name)
        for d in ds:
            demand(not (here / d).is_symlink(), "symlink directory: " + d)
        for f in fs:
            p = here / f
            regular(p)
            actual_files.add(p.relative_to(root).as_posix())
    demand(actual_files == set(expected_files) | {"MANIFEST.json"}, "exact selected file set mismatch")
    demand(actual_dirs == set(expected_dirs), "exact selected directory set mismatch")
    for name, item in expected_files.items():
        p = root / name
        info = regular(p)
        demand(stat.S_IMODE(info.st_mode) == item["mode"], "file mode mismatch: " + name)
        data = p.read_bytes()
        demand(len(data) == item["bytes"] and digest(data) == item["sha256"], "selected bytes mismatch: " + name)
    demand(digest((root / "FINAL.md").read_bytes()) == args.final_sha256, "detached FINAL anchor mismatch")
    ri = regular(report)
    demand(stat.S_IMODE(ri.st_mode) == manifest["outside_report_mode"], "REPORT mode mismatch")
    demand(digest(report.read_bytes()) == args.report_sha256, "detached REPORT anchor mismatch")
    return {"artifact_only": True, "selected_files": len(expected_files), "directories": len(expected_dirs),
            "manifest_sha256": args.manifest_sha256, "final_sha256": args.final_sha256,
            "outside_report_sha256": args.report_sha256, "mathematical_review": "not performed by this verifier"}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--manifest-sha256", required=True, type=valid_anchor)
    parser.add_argument("--final-sha256", required=True, type=valid_anchor)
    parser.add_argument("--report-sha256", required=True, type=valid_anchor)
    args = parser.parse_args()
    try:
        print(json.dumps(run(args), sort_keys=True))
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(json.dumps({"artifact_only": True, "error": str(exc)}), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
